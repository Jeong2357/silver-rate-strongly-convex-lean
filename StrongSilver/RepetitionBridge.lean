-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Schedules
import StrongSilver.Constants
import Mathlib.Analysis.SpecificLimits.Basic

namespace StrongSilver
open Filter
open scoped Topology
noncomputable section

theorem le_of_all_powers_le_multiple (a b K : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (h : ∀ r : ℕ, a^r ≤ K*b^r) : a ≤ b := by
  by_contra hn
  have hba : b/a < 1 := (div_lt_one ha).mpr (lt_of_not_ge hn)
  have hratio : 0 ≤ b/a := div_nonneg hb ha.le
  have hlim : Tendsto (fun r : ℕ => K*(b/a)^r) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio hba).const_mul K
  have hbound (r : ℕ) : 1 ≤ K*(b/a)^r := by
    calc
      1 = a^r/a^r := (div_self (pow_pos ha r).ne').symm
      _ ≤ (K*b^r)/a^r := div_le_div_of_nonneg_right (h r) (pow_pos ha r).le
      _ = K*(b/a)^r := by rw [div_pow]; ring
  have hfalse : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Eventually.of_forall hbound)
  linarith

/-- Repetition removes the condition-number prefactor in D ≤ κE. -/
theorem value_lower_of_repetitions {κ : ℝ} (hκ : 1 ≤ κ) (h : List ℝ) {a : ℝ} (ha : 0 < a)
    (hd : ∀ r : ℕ, ENNReal.ofReal (a^r) ≤ D κ (repeatSchedule h r)) :
    ENNReal.ofReal a ≤ E κ h := by
  by_cases ht : E κ h = ⊤
  · simp [ht]
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  apply (ENNReal.ofReal_le_iff_le_toReal ht).mpr
  apply le_of_all_powers_le_multiple a (E κ h).toReal κ ha ENNReal.toReal_nonneg
  intro r
  have hl := (hd r).trans ((D_le_kappa_E hκpos (repeatSchedule h r)).trans
    (mul_le_mul' le_rfl (E_repeat_le hκ h r)))
  have hf : ENNReal.ofReal κ * E κ h ^ r ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ht)
  have hr := ENNReal.toReal_mono hf hl
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (pow_pos ha r).le, ENNReal.toReal_ofReal hκpos.le] using hr

def DistanceLowerBound : Prop :=
  ∃ C κ₀ : ℝ, 0 < C ∧ 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ ≤ κ → ∀ h : List ℝ,
    ENNReal.ofReal (Real.exp (-C*(h.length : ℝ)*κ^(-nu))) ≤ D κ h

/-- Section 5.2: a uniform distance bound implies the same function-value bound. -/
theorem value_lower_of_distance_lower {κ C : ℝ} (hκ : 1 ≤ κ)
    (hd : ∀ h : List ℝ, ENNReal.ofReal (Real.exp (-C*(h.length : ℝ)*κ^(-nu))) ≤ D κ h)
    (h : List ℝ) : ENNReal.ofReal (Real.exp (-C*(h.length : ℝ)*κ^(-nu))) ≤ E κ h := by
  apply value_lower_of_repetitions hκ h (Real.exp_pos _)
  intro r
  have hr := hd (repeatSchedule h r)
  have he : Real.exp (-C*((repeatSchedule h r).length : ℝ)*κ^(-nu)) =
      Real.exp (-C*(h.length : ℝ)*κ^(-nu))^r := by
    rw [repeatSchedule_length, Nat.cast_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  rwa [he] at hr

/-- This is a reduction of the target; `DistanceLowerBound` is not yet proved here. -/
theorem main_iff_distance_lower : MainLowerBound ↔ DistanceLowerBound := by
  constructor
  · rintro ⟨C,κ₀,hC,hκ₀,hbound⟩
    exact ⟨C,κ₀,hC,hκ₀,fun κ hκ h => (hbound κ hκ h).1⟩
  · rintro ⟨C,κ₀,hC,hκ₀,hbound⟩
    refine ⟨C,max κ₀ 1,hC,hκ₀.trans_le (le_max_left _ _),fun κ hκ h => ?_⟩
    have hk0 : κ₀ ≤ κ := (le_max_left _ _).trans hκ
    have hk1 : 1 ≤ κ := (le_max_right _ _).trans hκ
    exact ⟨hbound κ hk0 h,value_lower_of_distance_lower hk1 (hbound κ hk0) h⟩

end
end StrongSilver
