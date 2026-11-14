-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarRootProjection
import StrongSilver.NegativePrefixProduct

namespace StrongSilver.PlanarBoundaryCertificate
open Set Complex Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2600000
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C

theorem physical_coordinates_nonnegative {x : ℂ} (hx : x ∈ C.domain) :
    0 ≤ (C.physical x).re ∧ 0 ≤ (C.physical x).im := by
  have hv := C.body.projection_mem x
  have hμ := (sub_pos.mpr C.mu_lt_one).le
  rw [physical_projection_formula]
  simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  exact ⟨add_nonneg (mul_nonneg C.mu_nonnegative hx.1) (mul_nonneg hμ (C.body_re_nonnegative hv)),
    add_nonneg (mul_nonneg C.mu_nonnegative hx.2.1) (mul_nonneg hμ (C.body_im_nonnegative hv))⟩

theorem nonnegative_step_norm_nonincrease {x y : ℂ} (hx : x ∈ C.domain) (hy : y ∈ C.domain)
    {b : ℝ} (hb : 0 ≤ b) (hu : y = x-b • C.physical x) : ‖y‖ ≤ ‖x‖ := by
  have hg := C.physical_coordinates_nonnegative hx
  have hxr : y.re ≤ x.re := by
    rw [hu,Complex.sub_re,Complex.smul_re,smul_eq_mul]
    exact sub_le_self _ (mul_nonneg hb hg.1)
  have hxi : y.im ≤ x.im := by
    rw [hu,Complex.sub_im,Complex.smul_im,smul_eq_mul]
    exact sub_le_self _ (mul_nonneg hb hg.2)
  have hnorm (z : ℂ) : ‖z‖^2 = z.re^2+z.im^2 := by
    rw [← real_inner_self_eq_norm_sq,complex_inner_coordinates]
    ring
  have h1 := mul_self_le_mul_self hy.1 hxr
  have h2 := mul_self_le_mul_self hy.2.1 hxi
  nlinarith only [h1,h2,hnorm x,hnorm y,norm_nonneg x,norm_nonneg y]

theorem negative_step_norm_growth {x y : ℂ} {b : ℝ} (hb : b ≤ 0)
    (hu : y = x-b • C.physical x) : ‖y‖ ≤ (1-μ*b)*‖x‖+2*(-b) := by
  have hm1 : 0 ≤ 1-μ := (sub_pos.mpr C.mu_lt_one).le
  have hden : 0 ≤ 1-μ*b := by have hh := mul_nonpos_of_nonneg_of_nonpos C.mu_nonnegative hb; linarith only [hh]
  have hcoef : 0 ≤ -b*(1-μ) := mul_nonneg (neg_nonneg.mpr hb) hm1
  have hv : ‖C.body.projection x‖ ≤ 2 := by
    have hh := C.body_norm_bound (C.body.projection_mem x)
    have hr : planarRadius A 0 ≤ 2 := by linarith [C.head_radius_bound,C.scale_le]
    exact hh.trans hr
  have he : y = (1-μ*b) • x+(-b*(1-μ)) • C.body.projection x := by
    rw [hu,physical_projection_formula]
    module
  have hn := norm_add_le ((1-μ*b) • x) ((-b*(1-μ)) • C.body.projection x)
  rw [← he] at hn
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hden,abs_of_nonneg hcoef] at hn
  have h1 := mul_le_mul_of_nonneg_left hv hcoef
  have h2 := mul_nonneg (neg_nonneg.mpr hb) C.mu_nonnegative
  nlinarith only [hn,h1,h2]

theorem signed_step_norm_growth {x y : ℂ} (hx : x ∈ C.domain) (hy : y ∈ C.domain)
    (b : ℝ) (hu : y = x-b • C.physical x) :
    ‖y‖ ≤ (1+μ*max (-b) 0)*‖x‖+2*max (-b) 0 := by
  by_cases hb : 0 ≤ b
  · rw [max_eq_right (neg_nonpos.mpr hb)]
    simpa only [mul_zero,add_zero,one_mul] using C.nonnegative_step_norm_nonincrease hx hy hb hu
  · rw [max_eq_left (by linarith only [hb])]
    have hh := C.negative_step_norm_growth (le_of_not_ge hb) hu
    nlinarith only [hh]

/-- Negative original steps alone pay for norm growth along a positive
planar trajectory; all nonnegative steps have been handled by monotonicity. -/
theorem signed_trajectory_norm_growth (h : List ℝ) (x : ℂ)
    (hstates : ∀ i : ℕ, i ≤ h.length → iterate (h.take i) C.physical x ∈ C.domain) :
    ‖iterate h C.physical x‖ ≤ Real.exp (μ*negativeMass h)*(‖x‖+2*negativeMass h) := by
  induction h generalizing x with
  | nil => simp [negativeMass]
  | cons b h ih =>
    let y := x-b • C.physical x
    have hx : x ∈ C.domain := by simpa only [List.take_zero,iterate_nil] using hstates 0 (by omega)
    have hy : y ∈ C.domain := by
      simpa only [List.take_succ_cons,List.take_zero,iterate_cons,iterate_nil] using hstates 1 (by simp)
    have htstates : ∀ i : ℕ, i ≤ h.length → iterate (h.take i) C.physical y ∈ C.domain := by
      intro i hi
      have hh := hstates (i+1) (by simp only [List.length_cons]; omega)
      simpa only [List.take_succ_cons,iterate_cons] using hh
    have ht := ih y htstates
    have hs := C.signed_step_norm_growth hx hy b rfl
    have hnb : 0 ≤ max (-b) 0 := le_max_right _ _
    have hnt := negativeMass_nonnegative h
    have hμnb := mul_nonneg C.mu_nonnegative hnb
    have he1 := Real.add_one_le_exp (μ*max (-b) 0)
    have he0 : 1 ≤ Real.exp (μ*max (-b) 0) := Real.one_le_exp_iff.mpr hμnb
    have h1 := mul_le_mul_of_nonneg_right he1 (norm_nonneg x)
    have h2 := mul_le_mul_of_nonneg_right he0
      (show 0 ≤ 2*max (-b) 0+2*negativeMass h by nlinarith only [hnb,hnt])
    have hbudget : ‖y‖+2*negativeMass h ≤
        Real.exp (μ*max (-b) 0)*(‖x‖+2*max (-b) 0+2*negativeMass h) := by
      nlinarith only [hs,h1,h2]
    have hm := mul_le_mul_of_nonneg_left hbudget (Real.exp_pos (μ*negativeMass h)).le
    calc
      ‖iterate (b::h) C.physical x‖ = ‖iterate h C.physical y‖ := rfl
      _ ≤ Real.exp (μ*negativeMass h)*(‖y‖+2*negativeMass h) := ht
      _ ≤ Real.exp (μ*negativeMass h)*
          (Real.exp (μ*max (-b) 0)*(‖x‖+2*max (-b) 0+2*negativeMass h)) := hm
      _ = Real.exp (μ*negativeMass (b::h))*(‖x‖+2*negativeMass (b::h)) := by
        simp only [negativeMass,List.map_cons,List.sum_cons]
        rw [← mul_assoc,← Real.exp_add]
        congr 1 <;> ring

end
end StrongSilver.PlanarBoundaryCertificate
