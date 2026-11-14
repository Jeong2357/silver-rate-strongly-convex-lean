-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinearBoundarySolution

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section

theorem inverseSlopePrimitive_monotoneOn {k₀ Θ : ℝ} (hk : 0 < k₀) (hΘ : Θ < Real.pi/2) :
    MonotoneOn (inverseSlopePrimitive k₀) (Icc (0 : ℝ) Θ) := by
  have hcos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2.trans_lt hΘ⟩
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) := inverseSlopePrimitive_hasDerivAt (k₀ := k₀) (hcos t ht).ne'
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht0 := interior_subset ht
  rw [(hd t ht0).deriv]
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi ht0.1 (by linarith [ht0.2,hΘ,Real.pi_pos])
  rw [Real.tan_eq_sin_div_cos]
  exact add_nonneg (inv_nonneg.mpr hk.le)
    (mul_nonneg (by norm_num) (div_nonneg hsin (hcos t ht0).le))

theorem inverseSlopePrimitive_nonnegative {k₀ Θ θ : ℝ} (hk : 0 < k₀) (hΘ : Θ < Real.pi/2)
    (hθ : θ ∈ Icc (0 : ℝ) Θ) : 0 ≤ inverseSlopePrimitive k₀ θ := by
  have hh := inverseSlopePrimitive_monotoneOn hk hΘ ⟨le_rfl,hθ.1.trans hθ.2⟩ hθ hθ.1
  simpa only [inverseSlopePrimitive,zero_div,Real.cos_zero,Real.log_one,mul_zero,sub_zero] using hh

theorem explicitArcRadius_uniform_upper {k₀ Θ R θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) (hR : 0 ≤ R) (hθ : θ ∈ Icc (0 : ℝ) Θ) :
    explicitArcRadius Θ R k₀ θ ≤ R*Real.exp (k₀*Θ) := by
  rw [explicitArcRadius_eq hk hk1 hΘ hθ]
  have hi : IntervalIntegrable (smoothPlanarSlope k₀) volume θ Θ := by
    apply ContinuousOn.intervalIntegrable_of_Icc hθ.2
    intro t ht
    exact (smoothPlanarSlope_continuousAt hk hk1 hΘ ⟨hθ.1.trans ht.1,ht.2⟩).continuousWithinAt
  have hb := (arcRadius_bounds hR hθ.2 (smoothPlanarSlope k₀) hi
    (fun t ht => ⟨(smoothPlanarSlope_bounds hk (hθ.1.trans ht.1) (ht.2.trans_lt hΘ)).1.le,
      (smoothPlanarSlope_bounds hk (hθ.1.trans ht.1) (ht.2.trans_lt hΘ)).2.1⟩)).2
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hk.le hθ.1])) hR)

theorem linearBoundarySolution_upper {k₀ Θ R θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) (hR : 0 ≤ R) (hθ : θ ∈ Icc (0 : ℝ) Θ) :
    linearBoundarySolution Θ R k₀ θ ≤
      R*Real.exp (k₀*Θ)*Θ*Real.exp (inverseSlopePrimitive k₀ Θ) := by
  let C := R*Real.exp (k₀*Θ)*Real.exp (inverseSlopePrimitive k₀ Θ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hHmono := inverseSlopePrimitive_monotoneOn hk hΘ
  have hpoint (t : ℝ) (ht : t ∈ Icc θ Θ) : linearBoundaryIntegrand Θ R k₀ t ≤ C := by
    have ht0 : t ∈ Icc (0 : ℝ) Θ := ⟨hθ.1.trans ht.1,ht.2⟩
    have hrb := explicitArcRadius_uniform_upper hk hk1 hΘ hR ht0
    have hHb := Real.exp_le_exp.mpr (hHmono ht0 ⟨hθ.1.trans hθ.2,le_rfl⟩ ht.2)
    exact mul_le_mul hrb hHb (Real.exp_pos _).le (mul_nonneg hR (Real.exp_pos _).le)
  have hD (t : ℝ) (ht : t ∈ Icc θ Θ) : Real.cos t+2*k₀*Real.sin t ≠ 0 := by
    have hh := smoothPlanar_denominator_lower hk hk1 ⟨hθ.1.trans ht.1,ht.2.trans hΘ.le⟩
    exact ne_of_gt (lt_of_lt_of_le (by linarith : 0 < 2*k₀) hh)
  have hcos (t : ℝ) (ht : t ∈ Icc θ Θ) : Real.cos t ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1,ht.1,Real.pi_pos],ht.2.trans_lt hΘ⟩).ne'
  have hi : IntervalIntegrable (linearBoundaryIntegrand Θ R k₀) volume θ Θ := by
    apply ContinuousOn.intervalIntegrable_of_Icc hθ.2
    exact fun t ht => (linearBoundaryIntegrand_continuousAt (hD t ht) (hcos t ht)).continuousWithinAt
  have hI := intervalIntegral.integral_mono_on hθ.2 hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume θ Θ) hpoint
  rw [intervalIntegral.integral_const] at hI
  simp only [smul_eq_mul] at hI
  have hI0 : 0 ≤ ∫ t in θ..Θ, linearBoundaryIntegrand Θ R k₀ t := by
    apply intervalIntegral.integral_nonneg hθ.2
    intro t ht
    exact mul_nonneg (mul_nonneg hR (Real.exp_pos _).le) (Real.exp_pos _).le
  have hexp : Real.exp (-inverseSlopePrimitive k₀ θ) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
      (neg_nonpos.mpr (inverseSlopePrimitive_nonnegative hk hΘ hθ))
  have hJ := mul_le_mul_of_nonneg_right hexp hI0
  simp only [one_mul] at hJ
  unfold linearBoundarySolution
  dsimp [C] at hI hC
  nlinarith only [hJ,hI,mul_nonneg hC hθ.1]

theorem exp_inverseSlopePrimitive {k₀ θ : ℝ} (hc : 0 < Real.cos θ) :
    Real.exp (inverseSlopePrimitive k₀ θ) = Real.exp (θ/k₀)*(Real.cos θ)⁻¹^2 := by
  unfold inverseSlopePrimitive
  rw [sub_eq_add_neg,Real.exp_add]
  congr 1
  calc
    Real.exp (-(2*Real.log (Real.cos θ))) = Real.exp (-Real.log (Real.cos θ))*Real.exp (-Real.log (Real.cos θ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = (Real.cos θ)⁻¹^2 := by rw [Real.exp_neg,Real.exp_log hc]; ring

theorem exp_inverseSlopePrimitive_terminal {k₀ ε : ℝ} :
    Real.exp (inverseSlopePrimitive k₀ (Real.arctan ε⁻¹)) =
      Real.exp (Real.arctan ε⁻¹/k₀)*(1+ε⁻¹^2) := by
  rw [exp_inverseSlopePrimitive (Real.cos_arctan_pos _)]
  have hh := Real.cos_sq_arctan ε⁻¹
  rw [inv_pow,hh]
  simp only [one_div,inv_inv]

end
end StrongSilver
