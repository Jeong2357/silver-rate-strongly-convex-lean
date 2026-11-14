-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusInterval

namespace StrongSilver.Scalar.Silver
open Set
noncomputable section
set_option maxHeartbeats 1000000

def logDistance (a b : ℝ) : ℝ := (Real.log (a/rho))^2+(Real.log (b/rho))^2
def localLogCoefficient : ℝ := hessianMargin*rho^2/16

theorem logDistance_nonnegative (a b : ℝ) : 0 ≤ logDistance a b := add_nonneg (sq_nonneg _) (sq_nonneg _)
theorem localLogCoefficient_positive : 0 < localLogCoefficient := by
  unfold localLogCoefficient
  exact div_pos (mul_pos hessianMargin_positive (sq_pos_of_pos rho_positive)) (by norm_num)

theorem localLogCoefficient_scaling : localLogCoefficient*(2/rho)^2=hessianMargin/4 := by
  unfold localLogCoefficient
  field_simp [rho_positive.ne'] <;> ring

theorem splitPotential_local_log : ∃ δ > 0, ∀ a b : ℝ, |a-rho| < δ → |b-rho| < δ →
    localLogCoefficient*logDistance a b ≤ splitPotential a b := by
  obtain ⟨d,hd,hlocal⟩ := splitPotential_local_lower
  let δ := min d (rho/2)
  have hδ : 0 < δ := lt_min hd (by linarith [rho_positive])
  refine ⟨δ,hδ,fun a b ha hb => ?_⟩
  have hδd : δ ≤ d := min_le_left _ _
  have hδr : δ ≤ rho/2 := min_le_right _ _
  have har : rho/2 ≤ a := by have h := (abs_lt.mp ha).1; linarith
  have hbr : rho/2 ≤ b := by have h := (abs_lt.mp hb).1; linarith
  have h1 := Calculus.log_ratio_sq_bound a rho rho_positive har
  have h2 := Calculus.log_ratio_sq_bound b rho rho_positive hbr
  have hlog : logDistance a b ≤ (2/rho)^2*((a-rho)^2+(b-rho)^2) := by unfold logDistance; nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hlog localLogCoefficient_positive.le
  rw [← mul_assoc,localLogCoefficient_scaling] at hweighted
  exact hweighted.trans (hlocal a b (ha.trans_le hδd) (hb.trans_le hδd))

/-- The normalized quantitative excess bound, including the deficit in the
parent mass. The constants are independent of all four masses. -/
theorem unitExcess_stability : ∃ c > 0, ∀ a b z : ℝ, 0 < a → 0 < b → a ≤ z → z ≤ a+b+1 →
    c*min 1 (logDistance a b+(a+b+1-z)) ≤ unitExcess a b z := by
  obtain ⟨d,hd,hlocal⟩ := splitPotential_local_log
  let δ := min d (min 1 ((rho-1)/2))
  have hδ : 0 < δ := lt_min hd (lt_min zero_lt_one (by linarith [rho_bounds.1]))
  have hδd : δ ≤ d := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ (rho-1)/2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨cAway,hcAway,haway⟩ := splitPotential_away δ hδ
  let cNear := min localLogCoefficient intervalSlope
  have hcNear : 0 < cNear := lt_min localLogCoefficient_positive intervalSlope_positive
  let c := min cNear (min minimum cAway)
  have hc : 0 < c := lt_min hcNear (lt_min minimum_positive hcAway)
  refine ⟨c,hc,fun a b z ha hb haz hz => ?_⟩
  have hell : 0 ≤ a+b+1-z := sub_nonneg.mpr hz
  have hcost : 0 ≤ logDistance a b+(a+b+1-z) := add_nonneg (logDistance_nonnegative _ _) hell
  by_cases hclose : |a-rho| < δ ∧ |b-rho| < δ
  · have h1 := hlocal a b (hclose.1.trans_le hδd) (hclose.2.trans_le hδd)
    have ha1 : 1 ≤ a := by have h := (abs_lt.mp hclose.1).1; linarith [rho_bounds.1]
    have hcap : a+b+1 ≤ 2*rho+3 := by
      have hA := (abs_lt.mp hclose.1).2
      have hB := (abs_lt.mp hclose.2).2
      linarith
    have h2 := unitExcess_deficit_lower a b z ha1 hb haz hz hcap
    have hnear : cNear*(logDistance a b+(a+b+1-z)) ≤ unitExcess a b z := by
      have hL := mul_le_mul_of_nonneg_right (min_le_left localLogCoefficient intervalSlope) (logDistance_nonnegative a b)
      have hD := mul_le_mul_of_nonneg_right (min_le_right localLogCoefficient intervalSlope) hell
      dsimp [cNear]
      nlinarith [hL,hD,h1,h2]
    calc
      _ ≤ c*(logDistance a b+(a+b+1-z)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
      _ ≤ cNear*(logDistance a b+(a+b+1-z)) := mul_le_mul_of_nonneg_right (min_le_left _ _) hcost
      _ ≤ _ := hnear
  · have hfar : δ ≤ |a-rho| ∨ δ ≤ |b-rho| := by
      by_contra hn
      push_neg at hn
      exact hclose ⟨hn.1,hn.2⟩
    have hF := haway a b ha hb hfar
    have hE := unitExcess_endpoint_lower a b z ha hb haz hz
    have hconst : c ≤ unitExcess a b z :=
      (min_le_right _ _).trans ((min_le_min_left minimum hF).trans hE)
    calc
      _ ≤ c*1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
      _ = c := mul_one c
      _ ≤ _ := hconst

end
end StrongSilver.Scalar.Silver
