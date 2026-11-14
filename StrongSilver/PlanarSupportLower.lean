-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarDomainGeometry
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace StrongSilver.PlanarBoundaryCertificate
open Set Real Complex
noncomputable section
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C
set_option maxHeartbeats 1000000

theorem radius_ge_one {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) : 1 ≤ planarRadius A θ := by
  have htR : 1 ≤ planarRadius A (planarTerminalAngle A) := by
    have hh := Complex.im_le_norm (polarArc (planarRadius A) (planarTerminalAngle A))
    rw [polarArc_norm (C.radius_pos _).le,C.arc_terminal] at hh
    exact hh
  exact htR.trans (C.radius_antitone ht ⟨C.angle_pos.le,le_rfl⟩ ht.2)

theorem complex_polar_decomposition (w : ℂ) : w = ‖w‖ • polarUnit w.arg := by
  apply Complex.ext
  · simpa only [polarUnit,Complex.smul_re,smul_eq_mul] using (Complex.norm_mul_cos_arg w).symm
  · simpa only [polarUnit,Complex.smul_im,smul_eq_mul] using (Complex.norm_mul_sin_arg w).symm

/-- The support function dominates the Euclidean norm in the first quadrant. -/
theorem supportValue_ge_norm {w : ℂ} (hx : 0 ≤ w.re) (hy : 0 ≤ w.im) : ‖w‖ ≤ C.body.supportValue w := by
  by_cases hw : w = 0
  · subst w
    rw [norm_zero,C.body.supportValue_zero]
  by_cases hsteep : w.re ≤ planarEpsilon A*w.im
  · have hs := C.body.inner_le_supportValue w (⟨planarEpsilon A,1⟩ : ℂ) C.body_terminal_mem
    simp only [complex_inner_coordinates] at hs
    have hn : ‖w‖^2 = w.re^2+w.im^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      ring
    have hprod := mul_le_mul_of_nonneg_left hsteep hx
    have hcross : 0 ≤ (planarEpsilon A*w.re)^2 := sq_nonneg _
    have hε1 : planarEpsilon A ≤ 1 := C.epsilon_slope.trans (by linarith [C.scale_le])
    have hlarge : w.re^2 ≤ 2*planarEpsilon A*w.re*w.im := by nlinarith only [hprod]
    have hl : ‖w‖ ≤ planarEpsilon A*w.re+w.im := by
      have hnonnegative := add_nonneg (mul_nonneg C.epsilon_pos.le hx) hy
      nlinarith only [hn,hcross,hlarge,hnonnegative,norm_nonneg w]
    nlinarith only [hl,hs]
  · have hxp : 0 < w.re := lt_of_le_of_lt (mul_nonneg C.epsilon_pos.le hy) (lt_of_not_ge hsteep)
    have harg0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hy
    have harglt : w.arg < Real.pi/2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hxp)
    have htan : w.im/w.re ≤ (planarEpsilon A)⁻¹ := by
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hxp C.epsilon_pos).mpr
      nlinarith only [le_of_not_ge hsteep]
    have harg : w.arg ≤ planarTerminalAngle A := by
      have hh := Real.arctan_mono htan
      rw [← Complex.tan_arg w,Real.arctan_tan (by linarith [Real.pi_pos]) harglt] at hh
      exact hh
    have ht : w.arg ∈ Icc (0 : ℝ) (planarTerminalAngle A) := ⟨harg0,harg⟩
    have hs := C.body.inner_le_supportValue w (polarArc (planarRadius A) w.arg)
      (polarArc_mem_body C.radius_continuousOn ht)
    have hi : inner ℝ w (polarArc (planarRadius A) w.arg) = ‖w‖*planarRadius A w.arg := by
      have he := congrArg (fun u : ℂ => inner ℝ u (polarArc (planarRadius A) w.arg))
        (C.complex_polar_decomposition w)
      rw [he]
      rw [polarArc,real_inner_smul_left,real_inner_smul_right,polarUnit_inner,sub_self,Real.cos_zero,mul_one]
    rw [hi] at hs
    exact (by nlinarith only [mul_le_mul_of_nonneg_left (C.radius_ge_one ht) (norm_nonneg w)] : ‖w‖ ≤ ‖w‖*planarRadius A w.arg).trans hs

theorem projection_residual_support_lower {z : ℂ} (hz : z ∈ C.domain) :
    ‖z-C.body.projection z‖ ≤ inner ℝ (C.body.projection z) (z-C.body.projection z) := by
  have hc := C.projection_residual_nonnegative hz
  have hh := C.supportValue_ge_norm hc.1 hc.2
  rwa [C.body.supportValue_projection_residual] at hh

end
end StrongSilver.PlanarBoundaryCertificate
