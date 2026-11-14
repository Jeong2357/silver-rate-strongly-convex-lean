-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ArcRadius
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section

def slopePrimitive (k₀ θ : ℝ) : ℝ :=
  (2*k₀^2/(1+4*k₀^2))*Real.log (Real.cos θ+2*k₀*Real.sin θ)+(k₀/(1+4*k₀^2))*θ

def inverseSlopePrimitive (k₀ θ : ℝ) : ℝ := θ/k₀-2*Real.log (Real.cos θ)

def explicitArcRadius (Θ R k₀ θ : ℝ) : ℝ :=
  R*Real.exp (slopePrimitive k₀ Θ-slopePrimitive k₀ θ)

theorem slopePrimitive_hasDerivAt {k₀ θ : ℝ} (hd : Real.cos θ+2*k₀*Real.sin θ ≠ 0) :
    HasDerivAt (slopePrimitive k₀) (smoothPlanarSlope k₀ θ) θ := by
  have hD := (Real.hasDerivAt_cos θ).add ((Real.hasDerivAt_sin θ).const_mul (2*k₀))
  have hh := ((hD.log hd).const_mul (2*k₀^2/(1+4*k₀^2))).add
    ((hasDerivAt_id θ).const_mul (k₀/(1+4*k₀^2)))
  simp only [Pi.add_apply,id_eq] at hh
  convert! hh using 1
  unfold smoothPlanarSlope
  have hq : 1+4*k₀^2 ≠ 0 := ne_of_gt (by positivity)
  have halg : k₀*Real.cos θ = (2*k₀^2/(1+4*k₀^2))*(-Real.sin θ+2*k₀*Real.cos θ)+
      (k₀/(1+4*k₀^2))*(Real.cos θ+2*k₀*Real.sin θ) := by
    field_simp [hq]
    <;> ring
  calc
    k₀*Real.cos θ/(Real.cos θ+2*k₀*Real.sin θ) =
        ((2*k₀^2/(1+4*k₀^2))*(-Real.sin θ+2*k₀*Real.cos θ)+
          (k₀/(1+4*k₀^2))*(Real.cos θ+2*k₀*Real.sin θ))/(Real.cos θ+2*k₀*Real.sin θ) := by rw [← halg]
    _ = _ := by rw [add_div,mul_div_assoc,mul_div_cancel_right₀ _ hd]; ring

theorem inverseSlopePrimitive_hasDerivAt {k₀ θ : ℝ} (hc : Real.cos θ ≠ 0) :
    HasDerivAt (inverseSlopePrimitive k₀) (k₀⁻¹+2*Real.tan θ) θ := by
  have hh := ((hasDerivAt_id θ).div_const k₀).sub (((Real.hasDerivAt_cos θ).log hc).const_mul 2)
  convert! hh using 1
  rw [Real.tan_eq_sin_div_cos]
  ring

theorem smoothPlanarSlope_integral {k₀ Θ θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) (hθ : θ ∈ Icc (0 : ℝ) Θ) :
    (∫ t in θ..Θ, smoothPlanarSlope k₀ t) = slopePrimitive k₀ Θ-slopePrimitive k₀ θ := by
  have hD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) : Real.cos t+2*k₀*Real.sin t ≠ 0 := by
    have hd := smoothPlanar_denominator_lower hk hk1 ⟨ht.1,ht.2.trans hΘ.le⟩
    exact ne_of_gt (lt_of_lt_of_le (by linarith : 0 < 2*k₀) hd)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hθ.2] at ht
    exact slopePrimitive_hasDerivAt (hD t ⟨hθ.1.trans ht.1,ht.2⟩)
  · apply ContinuousOn.intervalIntegrable_of_Icc hθ.2
    intro t ht
    exact (smoothPlanarSlope_hasDerivAt (hD t ⟨hθ.1.trans ht.1,ht.2⟩)).continuousAt.continuousWithinAt

theorem explicitArcRadius_eq {k₀ Θ R θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) (hθ : θ ∈ Icc (0 : ℝ) Θ) :
    explicitArcRadius Θ R k₀ θ = arcRadius Θ R (smoothPlanarSlope k₀) θ := by
  unfold explicitArcRadius arcRadius
  rw [smoothPlanarSlope_integral hk hk1 hΘ hθ]

theorem explicitArcRadius_stronglyMeasurable (Θ R k₀ : ℝ) : StronglyMeasurable (explicitArcRadius Θ R k₀) := by
  have hm : Measurable (explicitArcRadius Θ R k₀) := by unfold explicitArcRadius slopePrimitive; fun_prop
  exact hm.stronglyMeasurable

theorem explicitArcRadius_hasDerivAt {k₀ Θ R θ : ℝ} (hd : Real.cos θ+2*k₀*Real.sin θ ≠ 0) :
    HasDerivAt (explicitArcRadius Θ R k₀)
      (-smoothPlanarSlope k₀ θ*explicitArcRadius Θ R k₀ θ) θ := by
  have hh := (((slopePrimitive_hasDerivAt hd).const_sub (slopePrimitive k₀ Θ)).exp).const_mul R
  convert! hh using 1 <;> simp only [explicitArcRadius] <;> ring

theorem inverseSlope_integral {k₀ Θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ0 : 0 ≤ Θ) (hΘ : Θ < Real.pi/2) :
    (∫ t in (0 : ℝ)..Θ, (smoothPlanarSlope k₀ t)⁻¹) = Θ/k₀-2*Real.log (Real.cos Θ) := by
  have hcos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2.trans_lt hΘ⟩
  have hD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) : Real.cos t+2*k₀*Real.sin t ≠ 0 := by
    have hd := smoothPlanar_denominator_lower hk hk1 ⟨ht.1,ht.2.trans hΘ.le⟩
    exact ne_of_gt (lt_of_lt_of_le (by linarith : 0 < 2*k₀) hd)
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) :
      (smoothPlanarSlope k₀ t)⁻¹ = k₀⁻¹+2*Real.tan t := smoothPlanarSlope_inverse hk.ne' (hcos t ht).ne' (hD t ht)
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) Θ) :
      HasDerivAt (inverseSlopePrimitive k₀) ((smoothPlanarSlope k₀ t)⁻¹) t := by
    rw [uIcc_of_le hΘ0] at ht
    rw [he t ht]
    exact inverseSlopePrimitive_hasDerivAt (hcos t ht).ne'
  have hi : IntervalIntegrable (fun t => (smoothPlanarSlope k₀ t)⁻¹) volume 0 Θ := by
    apply ContinuousOn.intervalIntegrable_of_Icc hΘ0
    intro t ht
    exact ((smoothPlanarSlope_hasDerivAt (hD t ht)).continuousAt.inv₀
      (smoothPlanarSlope_bounds hk ht.1 (ht.2.trans_lt hΘ)).1.ne').continuousWithinAt
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simpa only [inverseSlopePrimitive,zero_div,Real.cos_zero,Real.log_one,mul_zero,sub_zero] using hI

end
end StrongSilver
