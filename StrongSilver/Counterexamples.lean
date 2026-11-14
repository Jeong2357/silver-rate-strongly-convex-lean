-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WeightedCountProperties
import StrongSilver.ErrorBounds
import StrongSilver.RepetitionBridge

namespace StrongSilver
open Filter
open scoped Topology
noncomputable section

def WeightedCountBound (a : ℝ) : Prop :=
  ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ κ : ℝ, K ≤ κ → ∀ h : List ℝ,
    1 ≤ h.length → D κ h ≤ 1 → weightedCount h (a*κ) ≤ C*(h.length : ℝ)

/-- The counterexample data in (2.1) use actual errors and actual schedules. -/
structure CounterexampleSequence (a : ℝ) where
  kappa : ℕ → ℝ
  schedules : ℕ → List ℝ
  kappa_ge_two : ∀ j, 2 ≤ kappa j
  length_pos : ∀ j, 1 ≤ (schedules j).length
  length_large : ∀ j, (kappa j)^nu ≤ ((schedules j).length : ℝ)
  distance_le_one : ∀ j, D (kappa j) (schedules j) ≤ 1
  weight_positive : ∀ j, 0 < weightedCount (schedules j) (a*kappa j)
  kappa_escape : Tendsto kappa atTop atTop
  ratio_escape : Tendsto
    (fun j => weightedCount (schedules j) (a*kappa j)/((schedules j).length : ℝ)) atTop atTop

theorem counterexample_of_not_weightedCountBound {a : ℝ} (ha : 0 < a) (hn : ¬WeightedCountBound a) :
    Nonempty (CounterexampleSequence a) := by
  classical
  have hex (j : ℕ) : ∃ κ : ℝ, (j : ℝ)+2 ≤ κ ∧ ∃ h : List ℝ,
      1 ≤ h.length ∧ D κ h ≤ 1 ∧ ((j : ℝ)+1)*(h.length : ℝ) < weightedCount h (a*κ) := by
    by_contra hbad
    apply hn
    refine ⟨(j : ℝ)+2,(j : ℝ)+1,by positivity,by positivity,?_⟩
    intro κ hκ h hlen hD
    by_contra hW
    exact hbad ⟨κ,hκ,h,hlen,hD,lt_of_not_ge hW⟩
  choose κ hκ raw hlen hD hW using hex
  let r : ℕ → ℕ := fun j => Nat.ceil ((κ j)^nu)+1
  let schedules : ℕ → List ℝ := fun j => repeatSchedule (raw j) (r j)
  have hrpos (j : ℕ) : 0 < r j := Nat.succ_pos _
  have hrreal (j : ℕ) : (0 : ℝ) < r j := by exact_mod_cast hrpos j
  have hk2 (j : ℕ) : 2 ≤ κ j := by linarith [hκ j, Nat.cast_nonneg (α := ℝ) j]
  have hkpos (j : ℕ) : 0 < κ j := lt_of_lt_of_le (by norm_num) (hk2 j)
  have hcap (j : ℕ) : 0 < a*κ j := mul_pos ha (hkpos j)
  have hlength (j : ℕ) : 1 ≤ (schedules j).length := by
    rw [show schedules j = repeatSchedule (raw j) (r j) from rfl,repeatSchedule_length]
    exact Nat.mul_pos (hrpos j) (hlen j)
  have hlengthreal (j : ℕ) : (0 : ℝ) < (schedules j).length := by
    exact_mod_cast hlength j
  have hlarge (j : ℕ) : (κ j)^nu ≤ ((schedules j).length : ℝ) := by
    have hceil : (κ j)^nu ≤ (r j : ℝ) := by
      have hc := Nat.le_ceil ((κ j)^nu)
      dsimp [r]
      push_cast
      linarith
    have hraw : (1 : ℝ) ≤ (raw j).length := by exact_mod_cast hlen j
    change (κ j)^nu ≤ ((repeatSchedule (raw j) (r j)).length : ℝ)
    rw [repeatSchedule_length,Nat.cast_mul]
    exact hceil.trans (by nlinarith [hrreal j])
  have hdist (j : ℕ) : D (κ j) (schedules j) ≤ 1 := by
    have hk1 : 1 ≤ κ j := by linarith [hk2 j]
    have hp := pow_le_pow_left' (hD j) (r j)
    simpa only [one_pow] using (D_repeat_le hk1 (raw j) (r j)).trans hp
  have hweight (j : ℕ) : ((j : ℝ)+1)*((schedules j).length : ℝ) <
      weightedCount (schedules j) (a*κ j) := by
    change ((j : ℝ)+1)*((repeatSchedule (raw j) (r j)).length : ℝ) <
      weightedCount (repeatSchedule (raw j) (r j)) (a*κ j)
    rw [weightedCount_repeat (raw j) (hcap j),repeatSchedule_length,Nat.cast_mul]
    have hh := mul_lt_mul_of_pos_left (hW j) (hrreal j)
    nlinarith only [hh]
  have hratio (j : ℕ) : (j : ℝ)+1 <
      weightedCount (schedules j) (a*κ j)/((schedules j).length : ℝ) :=
    (lt_div_iff₀ (hlengthreal j)).mpr (hweight j)
  have hNat : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hkT : Tendsto κ atTop atTop := by
    apply tendsto_atTop.mpr
    intro A
    filter_upwards [hNat.eventually_ge_atTop A] with j hj
    linarith [hκ j]
  have hrT : Tendsto
      (fun j => weightedCount (schedules j) (a*κ j)/((schedules j).length : ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro A
    filter_upwards [hNat.eventually_ge_atTop A] with j hj
    linarith [hratio j]
  refine ⟨⟨κ,schedules,hk2,hlength,hlarge,hdist,?_,hkT,hrT⟩⟩
  intro j
  exact lt_trans (mul_pos (by positivity) (hlengthreal j)) (hweight j)

end
end StrongSilver
