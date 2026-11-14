-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarConstruction

namespace StrongSilver
open Real Set
noncomputable section
set_option maxHeartbeats 1000000

def transformedGapMaximum (μ : ℝ) (h : List ℝ) : ℝ := -Real.log (minPrefixProduct μ h)/μ

theorem transformedGapMaximum_nonnegative {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) : 0 ≤ transformedGapMaximum μ h := by
  have hc := minPrefixProduct_positive h hh
  have hc1 : minPrefixProduct μ h ≤ 1 := by cases h <;> simp only [minPrefixProduct,min_le_left,le_refl]
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hc.le hc1)) hμ.le

theorem transformedGapMaximum_exp {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) :
    Real.exp (μ*transformedGapMaximum μ h) = (minPrefixProduct μ h)⁻¹ := by
  have he : μ*transformedGapMaximum μ h = -Real.log (minPrefixProduct μ h) := by
    unfold transformedGapMaximum
    exact mul_div_cancel₀ _ hμ.ne'
  rw [he,Real.exp_neg,Real.exp_log (minPrefixProduct_positive h hh)]

theorem exp_sub_one_le_mul_exp (t : ℝ) : Real.exp t-1 ≤ t*Real.exp t := by
  have he := Real.add_one_le_exp (-t)
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos t).le
  have hp : Real.exp (-t)*Real.exp t = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  rw [hp] at hm
  nlinarith only [hm]

namespace PlanarBoundaryCertificate
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)

/-- The planar start norm has the coefficient one needed for the silver rate. -/
theorem trajectory_norm_bound (hμ : 0 < μ) (h : List ℝ) (hh : ∀ b ∈ h, μ*b < 1) (R : ℂ)
    (hend : iterate h C.physical R = (⟨planarEpsilon A,1⟩ : ℂ))
    (hstates : ∀ i : ℕ, i ≤ h.length → iterate (h.take i) C.physical R ∈ C.domain) :
    ‖R‖ ≤ Real.exp (μ*transformedGapMaximum μ h)*
      (C.right+C.J 0+planarRadius A 0*transformedGapMaximum μ h) := by
  let m := transformedGapMaximum μ h
  let c := minPrefixProduct μ h
  have hm : 0 ≤ m := transformedGapMaximum_nonnegative hμ h hh
  have hc : 0 < c := minPrefixProduct_positive h hh
  have hexp : Real.exp (μ*m) = c⁻¹ := transformedGapMaximum_exp hμ h hh
  have hb := C.trajectory_prefix_bounds hμ h hh R hend hstates
  have hR : R ∈ C.domain := by simpa only [List.take_zero,iterate_nil] using hstates 0 (by omega)
  have hX : R.re+C.headShift ≤ (C.right+C.headShift)/c :=
    (le_div_iff₀ hc).mpr (by nlinarith only [hb.1])
  have hY : R.im ≤ C.J 0/c := (le_div_iff₀ hc).mpr (by nlinarith only [hb.2])
  have hn := Complex.norm_le_abs_re_add_abs_im R
  rw [abs_of_nonneg hR.1,abs_of_nonneg hR.2.1] at hn
  have hshift : C.headShift*μ = (1-μ)*planarRadius A 0 := by
    unfold headShift
    field_simp [hμ.ne']
  have hsexp := mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp (μ*m)) (C.headShift_nonnegative hμ)
  have hr := C.radius_pos 0
  have hpos : 0 ≤ μ*(planarRadius A 0*m*Real.exp (μ*m)) := by positivity
  have heq : C.headShift*(μ*m*Real.exp (μ*m)) = (1-μ)*planarRadius A 0*m*Real.exp (μ*m) := by
    rw [← hshift]
    ring
  rw [heq] at hsexp
  rw [div_eq_mul_inv,← hexp] at hX hY
  change ‖R‖ ≤ Real.exp (μ*m)*(C.right+C.J 0+planarRadius A 0*m)
  nlinarith only [hn,hX,hY,hsexp,hpos]

end PlanarBoundaryCertificate
end
end StrongSilver
