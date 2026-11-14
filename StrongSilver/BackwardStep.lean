-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.QuadraticCoercivity

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

def backwardPotential (h : ℝ) (F : V → ℝ) (x : V) : ℝ := (1/2)*‖x‖^2-h*F x

theorem backwardPotential_hasGradientAt (h : ℝ) (F : V → ℝ) (G : V → V)
    (hG : ∀ x, HasGradientAt F (G x) x) (x : V) :
    HasGradientAt (backwardPotential h F) (x-h • G x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! (quadratic_hasGradientAt (1 : ℝ) x).hasFDerivAt.sub
    ((hG x).hasFDerivAt.const_mul h) using 1
  ext y
  simp only [one_smul,map_sub,map_smul]

/-- Every noncritical GD step has a predecessor for a differentiable quadratic
plus a nonnegative perturbation with at most linear growth. -/
theorem exists_backward_step {μ h K : ℝ} (F : V → ℝ) (G : V → V)
    (hG : ∀ x, HasGradientAt F (G x) x)
    (hlower : ∀ x, (μ/2)*‖x‖^2 ≤ F x)
    (hupper : ∀ x, F x ≤ (μ/2)*‖x‖^2+K*‖x‖)
    (hcritical : 1-μ*h ≠ 0) (y : V) : ∃ x, x-h • G x = y := by
  have hdef (x : V) : |F x-(μ/2)*‖x‖^2| ≤ K*‖x‖ := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hlower x))]
    linarith only [hupper x]
  have hp (x : V) : |h*(F x-(μ/2)*‖x‖^2)| ≤ |h| * K*‖x‖ := by
    rw [abs_mul]
    nlinarith only [mul_le_mul_of_nonneg_left (hdef x) (abs_nonneg h)]
  by_cases hpos : 0 < 1-μ*h
  · have hΦ (x : V) : ((1-μ*h)/2)*‖x‖^2-(|h| * K)*‖x‖ ≤ backwardPotential h F x := by
      have hh := le_abs_self (h*(F x-(μ/2)*‖x‖^2))
      dsimp [backwardPotential]
      nlinarith only [hh,hp x]
    exact exists_gradient_preimage_of_quadratic_lower (backwardPotential h F)
      (fun x => x-h • G x) (backwardPotential_hasGradientAt h F G hG)
      (div_pos hpos (by norm_num)) hΦ y
  · have hneg : 1-μ*h < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hcritical
    have hΦ (x : V) : ((μ*h-1)/2)*‖x‖^2-(|h| * K)*‖x‖ ≤ -backwardPotential h F x := by
      have hh := neg_abs_le (h*(F x-(μ/2)*‖x‖^2))
      dsimp [backwardPotential]
      nlinarith only [hh,hp x]
    have hd (x : V) : HasGradientAt (fun z => -backwardPotential h F z) (-(x-h • G x)) x := by
      apply hasGradientAt_iff_hasFDerivAt.mpr
      convert! (backwardPotential_hasGradientAt h F G hG x).hasFDerivAt.neg using 1 <;>
        simp only [map_neg]
    obtain ⟨x,hx⟩ := exists_gradient_preimage_of_quadratic_lower
      (fun z => -backwardPotential h F z) (fun x => -(x-h • G x)) hd
      (div_pos (by linarith : 0 < μ*h-1) (by norm_num)) hΦ (-y)
    exact ⟨x,neg_injective hx⟩

end
end StrongSilver
