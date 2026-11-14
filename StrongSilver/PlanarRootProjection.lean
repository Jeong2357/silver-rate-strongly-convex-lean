-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LocalPhaseGeometry
import StrongSilver.PlanarSupportLower

namespace StrongSilver.PlanarBoundaryCertificate
open Set Complex
noncomputable section
set_option maxHeartbeats 2200000
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C

theorem physical_projection_formula (x : ℂ) : C.physical x = μ • x+(1-μ) • C.body.projection x := by
  unfold physical stronglyConvexGradient
  rw [C.body.support_envelope_gradient]

/-- A positive step longer than one cannot be taken inside the body
while remaining in the nonnegative domain. Its projection has norm at
least one, by the proved support lower bound. -/
theorem root_projection_norm_lower {x y : ℂ} (hx : x ∈ C.domain) (hy : y ∈ C.domain)
    (hxn : x ≠ 0) {b : ℝ} (hb : 1 < b) (hu : y = x-b • C.physical x) :
    1 ≤ ‖C.body.projection x‖ := by
  by_contra hp
  have hp1 : ‖C.body.projection x‖ < 1 := lt_of_not_ge hp
  have hs := C.projection_residual_support_lower hx
  have hc := real_inner_le_norm (C.body.projection x) (x-C.body.projection x)
  have hzero : ‖x-C.body.projection x‖ = 0 := by
    have hnon := norm_nonneg (x-C.body.projection x)
    by_contra hn
    have hpos : 0 < ‖x-C.body.projection x‖ := lt_of_le_of_ne hnon (Ne.symm hn)
    have hh := mul_pos (sub_pos.mpr hp1) hpos
    nlinarith only [hs,hc,hh]
  have hxv : x = C.body.projection x := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have hg : C.physical x = x := by
    rw [physical_projection_formula,← hxv]
    module
  have hey : y = (1-b) • x := by rw [hu,hg]; module
  have hi := complex_inner_nonnegative hx.1 hx.2.1 hy.1 hy.2.1
  rw [hey,real_inner_smul_right,real_inner_self_eq_norm_sq] at hi
  have hnorm : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hxn)
  have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr hb) hnorm
  linarith only [hi,hneg]

theorem root_state_norm_lower {x y : ℂ} (hx : x ∈ C.domain) (hy : y ∈ C.domain)
    (hxn : x ≠ 0) {b : ℝ} (hb : 1 < b) (hμ : μ ≤ 1/2) (hμb : μ*b < 1)
    (hu : y = x-b • C.physical x) : b/2 ≤ ‖x‖ := by
  have hvnorm := C.root_projection_norm_lower hx hy hxn hb hu
  have hv := C.body.projection_mem x
  have hyv := complex_inner_nonnegative hy.1 hy.2.1 (C.body_re_nonnegative hv) (C.body_im_nonnegative hv)
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hs : 0 ≤ b*(1-μ) := mul_nonneg hb0.le (by linarith only [hμ])
  have hden : 0 < 1-μ*b := sub_pos.mpr hμb
  have he : (1-μ*b) • x = y+(b*(1-μ)) • C.body.projection x := by
    rw [hu,physical_projection_formula]
    module
  have hi : 0 ≤ inner ℝ y ((b*(1-μ)) • C.body.projection x) := by
    rw [real_inner_smul_right]
    exact mul_nonneg hs hyv
  have hn := norm_add_sq_real y ((b*(1-μ)) • C.body.projection x)
  have hsum : ‖(b*(1-μ)) • C.body.projection x‖ ≤ ‖y+(b*(1-μ)) • C.body.projection x‖ := by
    nlinarith only [hn,hi,sq_nonneg ‖y‖,norm_nonneg ((b*(1-μ)) • C.body.projection x),
      norm_nonneg (y+(b*(1-μ)) • C.body.projection x)]
  rw [← he] at hsum
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs,abs_of_nonneg hden.le] at hsum
  have h1 := mul_le_mul_of_nonneg_left hvnorm hs
  have h2 := mul_nonneg (mul_nonneg C.mu_nonnegative hb0.le) (norm_nonneg x)
  have h3 := mul_le_mul_of_nonneg_left hμ hb0.le
  nlinarith only [hsum,h1,h2,h3]

end
end StrongSilver.PlanarBoundaryCertificate
