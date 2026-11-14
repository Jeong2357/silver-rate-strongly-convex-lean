-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianGroupScaleSeparation
import StrongSilver.CartesianUniformExteriorTime

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3000000

@[simp] theorem firstScale_append (μ : ℝ) (ps qs : List Group) (H : ℝ) :
    firstScale μ (ps++qs) H = firstScale μ ps (firstScale μ qs H) := by cases ps <;> rfl
@[simp] theorem firstOffset_append (ps qs : List Group) (Z : ℝ) :
    firstOffset (ps++qs) Z = firstOffset ps (firstOffset qs Z) := by cases ps <;> rfl

theorem sequenceReady_append (δ c μ ε : ℝ) (ps qs : List Group) (H Z : ℝ) :
    sequenceReady δ c μ ε (ps++qs) H Z ↔
      sequenceReady δ c μ ε ps (firstScale μ qs H) (firstOffset qs Z) ∧
      sequenceReady δ c μ ε qs H Z := by
  induction ps with
  | nil => simp [sequenceReady]
  | cons p ps ih =>
    simp only [List.cons_append,sequenceReady,firstScale_append,firstOffset_append,ih]
    exact and_assoc.symm

/-- Uniform scale budgets discharge every numeric joining condition of
an actual group. In particular, neither the negative-step condition nor
the retained height-offset condition remains a per-trajectory premise. -/
theorem groupReady_of_uniform_budgets {δ c μ ε B L U H Z Zmax : ℝ} {q : Group}
    (D : BalancedGroupData q.1 μ (groupScale μ q) q.2 ε)
    (hnear : ε+μ*groupScale μ q ≤ δ) (hμB : μ*B ≤ 1/2)
    (hL : 0 < L) (hU : 0 ≤ U) (hc : 0 ≤ c)
    (hTL : L ≤ groupScale μ q) (hbU : q.2 ≤ U) (hHlow : L ≤ H)
    (hHup : H ≤ (9/20:ℝ)*cappedStep μ B q.2)
    (hTklo : (19/20:ℝ)*cappedStep μ B q.2 ≤
      groupScale μ q*lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2))
    (hTkhi : groupScale μ q*lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2) ≤ 2*q.2)
    (hnegative : ∀ i : Fin 3, 2*U*negativeMass (q.1.gaps i.castSucc) ≤ c*L^2)
    (hZ : 0 ≤ Z) (hZmax : Z ≤ Zmax) (hZbudget : 2*U*Zmax ≤ c*L) :
    GroupReady δ c μ ε q H Z := by
  have hφ := cappedStep_ge D.mu_positive (show μ*B < 1 by linarith only [hμB]) q.2
  have hφpos : 0 < cappedStep μ B q.2 := by linarith only [hφ,D.exterior_lower]
  have hTpos := zero_lt_one.trans_le D.scale_lower
  have hk : 0 < lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2) := by
    have hp : 0 < groupScale μ q*lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2) := by
      nlinarith only [hTklo,hφpos]
    exact (mul_pos_iff.mp hp).elim (fun h => h.2) (fun h => False.elim ((not_lt_of_ge hTpos.le) h.1))
  have hkU : L*lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2) ≤ 2*U := by
    have hp := mul_le_mul_of_nonneg_right hTL hk.le
    linarith only [hp,hTkhi,hbU]
  exact ⟨D,hnear,joining_scale_condition hφpos.le hHup hTklo,
    uniform_offset_join hZ hL hU hkU hZmax hZbudget,
    fun i => uniform_negative_join (negativeMass_nonnegative _) hL hk hc hHlow hkU (hnegative i)⟩

end
end StrongSilver.ScheduleTree.FourGapGroup
