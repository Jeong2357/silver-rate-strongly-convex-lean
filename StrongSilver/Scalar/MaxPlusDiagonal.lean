-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusRatio
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace StrongSilver.Scalar.Silver
open Set
noncomputable section
set_option maxHeartbeats 800000

def diagonalPotential (x : ℝ) : ℝ := 2*scalarPotential x-scalarPotential (2*x+1)
def diagonalSlope (x : ℝ) : ℝ := 2*(x+1)/(x*(2*x+1))

theorem diagonalPotential_derivative (x : ℝ) (hx : 0 < x) :
    HasDerivAt diagonalPotential (diagonalSlope x*(diagonalRatio x-coefficient)) x := by
  have hinner : HasDerivAt (fun y : ℝ => 2*y+1) 2 x := by convert! ((hasDerivAt_id x).const_mul 2).add_const 1 using 1 <;> simp
  have h := ((scalarPotential_derivative x hx).const_mul 2).sub
    ((scalarPotential_derivative (2*x+1) (by linarith)).comp x hinner)
  convert! h using 1 <;> try rfl
  unfold diagonalSlope diagonalRatio scalarFirst
  have hu : 2*x+1 ≠ 0 := by linarith
  have hd : 1+1/x ≠ 0 := by have := one_div_pos.mpr hx; linarith
  field_simp [hx.ne',hu,hd] <;> ring

theorem diagonalSlope_positive (x : ℝ) (hx : 0 < x) : 0 < diagonalSlope x :=
  div_pos (by linarith) (mul_pos hx (by linarith))

theorem diagonalPotential_at_rho : diagonalPotential rho=0 := by
  unfold diagonalPotential scalarPotential
  rw [← rho_square,rho_rpow_nu,rho_square_rpow_nu,Real.log_pow]
  ring

theorem diagonal_derivative_negative (x : ℝ) (hx : 0 < x) (hxr : x < rho) :
    diagonalSlope x*(diagonalRatio x-coefficient) < 0 := by
  have hratio := diagonalRatio_strictMono hx rho_positive hxr
  rw [diagonalRatio_at_rho] at hratio
  exact mul_neg_of_pos_of_neg (diagonalSlope_positive x hx) (sub_neg.mpr hratio)

theorem diagonal_derivative_positive (x : ℝ) (hxr : rho < x) :
    0 < diagonalSlope x*(diagonalRatio x-coefficient) := by
  have hx := rho_positive.trans hxr
  have hratio := diagonalRatio_strictMono rho_positive hx hxr
  rw [diagonalRatio_at_rho] at hratio
  exact mul_pos (diagonalSlope_positive x hx) (sub_pos.mpr hratio)

/-- The one-dimensional minimum is exactly zero, and is unique. -/
theorem diagonalPotential_positive (x : ℝ) (hx : 0 < x) (hne : x ≠ rho) : 0 < diagonalPotential x := by
  have hcont (a b : ℝ) (ha : 0 < a) : ContinuousOn diagonalPotential (Icc a b) := by
    intro u hu
    exact (diagonalPotential_derivative u (ha.trans_le hu.1)).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne hne with hxr | hrx
  · obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope diagonalPotential
      (fun v => diagonalSlope v*(diagonalRatio v-coefficient)) hxr (hcont x rho hx)
      (fun v hv => diagonalPotential_derivative v (hx.trans hv.1))
    have hneg := diagonal_derivative_negative u (hx.trans hu.1) hu.2
    rw [he,diagonalPotential_at_rho,zero_sub] at hneg
    have hnum : -diagonalPotential x < 0 := by
      have hh := (div_lt_iff₀ (sub_pos.mpr hxr)).mp hneg
      simpa only [zero_mul] using hh
    linarith
  · obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope diagonalPotential
      (fun v => diagonalSlope v*(diagonalRatio v-coefficient)) hrx (hcont rho x rho_positive)
      (fun v hv => diagonalPotential_derivative v (rho_positive.trans hv.1))
    have hpos := diagonal_derivative_positive u hu.1
    rw [he,diagonalPotential_at_rho,sub_zero] at hpos
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hrx)).mp hpos

theorem diagonalPotential_nonnegative (x : ℝ) (hx : 0 < x) : 0 ≤ diagonalPotential x := by
  by_cases he : x=rho
  · rw [he,diagonalPotential_at_rho]
  · exact (diagonalPotential_positive x hx he).le

theorem scalarFirst_at_rho : scalarFirst rho=scalarFirst (rho^2) := by
  have h := diagonalPotential_derivative rho rho_positive
  have h' := ((scalarPotential_derivative rho rho_positive).const_mul 2).sub
    ((scalarPotential_derivative (2*rho+1) (by linarith [rho_positive])).comp rho
      (by convert! ((hasDerivAt_id rho).const_mul 2).add_const 1 using 1 <;> simp))
  have he := h.unique h'
  rw [diagonalRatio_at_rho,sub_self,mul_zero,← rho_square] at he
  linarith

end
end StrongSilver.Scalar.Silver
