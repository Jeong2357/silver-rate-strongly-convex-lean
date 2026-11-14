-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarArc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section

def arcRadius (Θ R : ℝ) (k : ℝ → ℝ) (θ : ℝ) : ℝ := R*Real.exp (∫ t in θ..Θ, k t)

theorem arcRadius_pos {Θ R θ : ℝ} (hR : 0 < R) (k : ℝ → ℝ) : 0 < arcRadius Θ R k θ :=
  mul_pos hR (Real.exp_pos _)

@[simp] theorem arcRadius_terminal (Θ R : ℝ) (k : ℝ → ℝ) : arcRadius Θ R k Θ = R := by
  simp only [arcRadius,intervalIntegral.integral_same,Real.exp_zero,mul_one]

theorem arcRadius_hasDerivAt {Θ R θ : ℝ} {k : ℝ → ℝ}
    (hi : IntervalIntegrable k volume θ Θ) (hm : StronglyMeasurable k) (hc : ContinuousAt k θ) :
    HasDerivAt (arcRadius Θ R k) (-k θ*arcRadius Θ R k θ) θ := by
  have hd := (intervalIntegral.integral_hasDerivAt_left hi hm.stronglyMeasurableAtFilter hc).exp
  convert! hd.const_mul R using 1 <;> simp only [arcRadius] <;> ring

theorem arcRadius_bounds {Θ R θ k₀ : ℝ} (hR : 0 ≤ R) (hθ : θ ≤ Θ) (k : ℝ → ℝ)
    (hi : IntervalIntegrable k volume θ Θ) (hk : ∀ t ∈ Icc θ Θ, 0 ≤ k t ∧ k t ≤ k₀) :
    R ≤ arcRadius Θ R k θ ∧ arcRadius Θ R k θ ≤ R*Real.exp (k₀*(Θ-θ)) := by
  have hnonneg : 0 ≤ ∫ t in θ..Θ, k t :=
    intervalIntegral.integral_nonneg hθ (fun t ht => (hk t ht).1)
  have hupper := intervalIntegral.integral_mono_on hθ hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => k₀) volume θ Θ)
    (fun t ht => (hk t ht).2)
  rw [intervalIntegral.integral_const] at hupper
  simp only [smul_eq_mul] at hupper
  constructor
  · exact le_mul_of_one_le_right hR (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnonneg)
  · unfold arcRadius
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hR
    nlinarith only [hupper]

theorem smoothPlanarSlope_stronglyMeasurable (k₀ : ℝ) : StronglyMeasurable (smoothPlanarSlope k₀) := by
  have hm : Measurable (smoothPlanarSlope k₀) := by unfold smoothPlanarSlope; fun_prop
  exact hm.stronglyMeasurable

theorem smoothPlanarSlope_continuousAt {k₀ Θ θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) (hθ : θ ∈ Icc (0 : ℝ) Θ) : ContinuousAt (smoothPlanarSlope k₀) θ := by
  have hd := smoothPlanar_denominator_lower hk hk1 ⟨hθ.1,hθ.2.trans hΘ.le⟩
  exact (smoothPlanarSlope_hasDerivAt (ne_of_gt (lt_of_lt_of_le (by linarith : 0 < 2*k₀) hd))).continuousAt

theorem smoothArcRadius_hasDerivAt {k₀ Θ R θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) (hθ : θ ∈ Icc (0 : ℝ) Θ) :
    HasDerivAt (arcRadius Θ R (smoothPlanarSlope k₀))
      (-smoothPlanarSlope k₀ θ*arcRadius Θ R (smoothPlanarSlope k₀) θ) θ := by
  apply arcRadius_hasDerivAt _ (smoothPlanarSlope_stronglyMeasurable k₀)
    (smoothPlanarSlope_continuousAt hk hk1 hΘ hθ)
  apply ContinuousOn.intervalIntegrable_of_Icc hθ.2
  intro t ht
  exact (smoothPlanarSlope_continuousAt hk hk1 hΘ ⟨hθ.1.trans ht.1,ht.2⟩).continuousWithinAt

theorem smoothPolarArc_support {k₀ Θ R : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) (hR : 0 ≤ R) {θ s : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) Θ) (hs : s ∈ Icc (0 : ℝ) Θ) :
    inner ℝ (polarNormal (smoothPlanarSlope k₀ θ) θ)
      (polarArc (arcRadius Θ R (smoothPlanarSlope k₀)) s) ≤
    inner ℝ (polarNormal (smoothPlanarSlope k₀ θ) θ)
      (polarArc (arcRadius Θ R (smoothPlanarSlope k₀)) θ) := by
  apply polarArc_support (fun s hs => smoothArcRadius_hasDerivAt hk hk1 hΘ hs)
    (fun s hs => mul_nonneg hR (Real.exp_pos _).le)
    (smoothNormalAngle_strictMonoOn hk hk1 hΘ).monotoneOn
    (fun s hs => ⟨(smoothNormalAngle_first_quadrant hk hs.1 (hs.2.trans_lt hΘ)).1,
      (smoothNormalAngle_first_quadrant hk hs.1 (hs.2.trans_lt hΘ)).2.le⟩) hθ hs

end
end StrongSilver
