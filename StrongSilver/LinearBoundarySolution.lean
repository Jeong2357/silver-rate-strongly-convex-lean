-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmoothPlanarPrimitives

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section

def linearBoundaryIntegrand (Θ R k₀ t : ℝ) : ℝ :=
  explicitArcRadius Θ R k₀ t*Real.exp (inverseSlopePrimitive k₀ t)

def linearBoundarySolution (Θ R k₀ θ : ℝ) : ℝ :=
  Real.exp (-inverseSlopePrimitive k₀ θ)*(∫ t in θ..Θ, linearBoundaryIntegrand Θ R k₀ t)

theorem linearBoundaryIntegrand_stronglyMeasurable (Θ R k₀ : ℝ) :
    StronglyMeasurable (linearBoundaryIntegrand Θ R k₀) := by
  have hm : Measurable (linearBoundaryIntegrand Θ R k₀) := by
    unfold linearBoundaryIntegrand explicitArcRadius slopePrimitive inverseSlopePrimitive
    fun_prop
  exact hm.stronglyMeasurable

theorem linearBoundaryIntegrand_continuousAt {Θ R k₀ t : ℝ}
    (hd : Real.cos t+2*k₀*Real.sin t ≠ 0) (hc : Real.cos t ≠ 0) :
    ContinuousAt (linearBoundaryIntegrand Θ R k₀) t :=
  (explicitArcRadius_hasDerivAt (Θ := Θ) (R := R) hd).continuousAt.mul
    ((inverseSlopePrimitive_hasDerivAt (k₀ := k₀) hc).exp).continuousAt

@[simp] theorem linearBoundarySolution_terminal (Θ R k₀ : ℝ) : linearBoundarySolution Θ R k₀ Θ = 0 := by
  simp only [linearBoundarySolution,intervalIntegral.integral_same,mul_zero]

theorem linearBoundarySolution_hasDerivAt {Θ R k₀ θ : ℝ}
    (hi : IntervalIntegrable (linearBoundaryIntegrand Θ R k₀) volume θ Θ)
    (hk : k₀ ≠ 0) (hd : Real.cos θ+2*k₀*Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) :
    HasDerivAt (linearBoundarySolution Θ R k₀)
      (-explicitArcRadius Θ R k₀ θ-linearBoundarySolution Θ R k₀ θ/smoothPlanarSlope k₀ θ) θ := by
  have hI := intervalIntegral.integral_hasDerivAt_left hi
    (linearBoundaryIntegrand_stronglyMeasurable Θ R k₀).stronglyMeasurableAtFilter
    (linearBoundaryIntegrand_continuousAt hd hc)
  have hH := (inverseSlopePrimitive_hasDerivAt (k₀ := k₀) hc).neg.exp
  have hh := hH.mul hI
  convert! hh using 1
  simp only [linearBoundarySolution,linearBoundaryIntegrand,Pi.neg_apply]
  have he := Real.exp_neg (inverseSlopePrimitive k₀ θ)
  have hn := (Real.exp_pos (inverseSlopePrimitive k₀ θ)).ne'
  have hkval : (smoothPlanarSlope k₀ θ)⁻¹ = k₀⁻¹+2*Real.tan θ := smoothPlanarSlope_inverse hk hc hd
  rw [div_eq_mul_inv,hkval]
  simp only [he]
  field_simp [hk,hn]
  <;> ring

theorem linearBoundarySolution_nonnegative {Θ R k₀ θ : ℝ} (hR : 0 ≤ R) (hθ : θ ≤ Θ) :
    0 ≤ linearBoundarySolution Θ R k₀ θ := by
  apply mul_nonneg (Real.exp_pos _).le
  apply intervalIntegral.integral_nonneg hθ
  intro t ht
  exact mul_nonneg (mul_nonneg hR (Real.exp_pos _).le) (Real.exp_pos _).le

theorem smoothLinearBoundarySolution_hasDerivAt {Θ R k₀ θ : ℝ}
    (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2) (hΘ : Θ < Real.pi/2) (hθ : θ ∈ Icc (0 : ℝ) Θ) :
    HasDerivAt (linearBoundarySolution Θ R k₀)
      (-explicitArcRadius Θ R k₀ θ-linearBoundarySolution Θ R k₀ θ/smoothPlanarSlope k₀ θ) θ := by
  have hD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) : Real.cos t+2*k₀*Real.sin t ≠ 0 := by
    have hd := smoothPlanar_denominator_lower hk hk1 ⟨ht.1,ht.2.trans hΘ.le⟩
    exact ne_of_gt (lt_of_lt_of_le (by linarith : 0 < 2*k₀) hd)
  have hC (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) : Real.cos t ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2.trans_lt hΘ⟩).ne'
  apply linearBoundarySolution_hasDerivAt _ hk.ne' (hD θ hθ) (hC θ hθ)
  apply ContinuousOn.intervalIntegrable_of_Icc hθ.2
  intro t ht
  exact (linearBoundaryIntegrand_continuousAt (hD t ⟨hθ.1.trans ht.1,ht.2⟩)
    (hC t ⟨hθ.1.trans ht.1,ht.2⟩)).continuousWithinAt

end
end StrongSilver
