-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarDomainGraph

namespace StrongSilver.PlanarBoundaryCertificate
open Set Real Complex
noncomputable section
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C
set_option maxHeartbeats 1000000

theorem body_linear_upper (N : ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hs : ∀ θ ∈ Icc (0 : ℝ) (planarTerminalAngle A), inner ℝ N (polarArc (planarRadius A) θ) ≤ a) :
    ∀ v ∈ C.body.carrier, inner ℝ N v ≤ a := by
  apply bodyOfCompact_inner_le
    ((isCompact_Icc.image_of_continuousOn (polarArc_continuousOn C.radius_continuousOn)).insert 0)
    (mem_insert (0 : ℂ) _) N a
  intro v hv
  rcases mem_insert_iff.mp hv with rfl | hv
  · simpa only [inner_zero_right] using ha
  · obtain ⟨θ,ht,rfl⟩ := hv
    exact hs θ ht

theorem radius_antitone : AntitoneOn (planarRadius A) (Icc (0 : ℝ) (planarTerminalAngle A)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) C.radius_continuousOn
    (fun θ ht => (C.radius_hasDerivAt (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro θ ht
  have ht0 := interior_subset ht
  rw [(C.radius_hasDerivAt ht0).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (C.slope_pos ht0).le) (C.radius_pos θ).le

theorem body_norm_bound {v : ℂ} (hv : v ∈ C.body.carrier) : ‖v‖ ≤ planarRadius A 0 := by
  apply bodyOfCompact_norm_bound
    ((isCompact_Icc.image_of_continuousOn (polarArc_continuousOn C.radius_continuousOn)).insert 0)
    (mem_insert (0 : ℂ) _) (M := planarRadius A 0) _ v hv
  intro w hw
  rcases mem_insert_iff.mp hw with rfl | hw
  · simpa only [norm_zero] using (C.radius_pos 0).le
  · obtain ⟨θ,ht,rfl⟩ := hw
    rw [polarArc_norm (C.radius_pos θ).le]
    exact C.radius_antitone ⟨le_rfl,C.angle_pos.le⟩ ht ht.1

theorem body_re_upper {v : ℂ} (hv : v ∈ C.body.carrier) : v.re ≤ planarRadius A 0 :=
  (Complex.re_le_norm v).trans (C.body_norm_bound hv)

theorem body_re_nonnegative {v : ℂ} (hv : v ∈ C.body.carrier) : 0 ≤ v.re := by
  have hh := C.body_linear_upper (⟨-1,0⟩ : ℂ) 0 le_rfl (fun θ ht => by
    have hc : 0 ≤ Real.cos θ := (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2.trans_lt C.angle_lt⟩).le
    simp only [complex_inner_coordinates,polarArc,polarUnit,Complex.smul_re,Complex.smul_im,smul_eq_mul,
      neg_one_mul,zero_mul,add_zero]
    exact neg_nonpos.mpr (mul_nonneg (C.radius_pos θ).le hc)) v hv
  simp only [complex_inner_coordinates,neg_one_mul,zero_mul,add_zero] at hh
  linarith

theorem body_im_nonnegative {v : ℂ} (hv : v ∈ C.body.carrier) : 0 ≤ v.im := by
  have hh := C.body_linear_upper (⟨0,-1⟩ : ℂ) 0 le_rfl (fun θ ht => by
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2,C.angle_lt,Real.pi_pos])
    simp only [complex_inner_coordinates,polarArc,polarUnit,Complex.smul_re,Complex.smul_im,smul_eq_mul,
      neg_one_mul,zero_mul,zero_add]
    exact neg_nonpos.mpr (mul_nonneg (C.radius_pos θ).le hs)) v hv
  simp only [complex_inner_coordinates,neg_one_mul,zero_mul,zero_add] at hh
  linarith

theorem body_terminal_mem : (⟨planarEpsilon A,1⟩ : ℂ) ∈ C.body.carrier := by
  have hp := polarArc_mem_body C.radius_continuousOn ⟨C.angle_pos.le,le_rfl⟩
  have he := C.curve_terminal
  rw [curve,planarBoundaryCurve_terminal C.terminal] at he
  rw [he] at hp
  exact hp

theorem body_head_mem : (⟨planarRadius A 0,0⟩ : ℂ) ∈ C.body.carrier := by
  have hp := polarArc_mem_body C.radius_continuousOn (show (0 : ℝ) ∈ Icc (0 : ℝ) (planarTerminalAngle A) from ⟨le_rfl,C.angle_pos.le⟩)
  have he : polarArc (planarRadius A) 0 = (⟨planarRadius A 0,0⟩ : ℂ) := by
    apply Complex.ext <;> simp only [polarArc,polarUnit,Real.cos_zero,Real.sin_zero,
      Complex.smul_re,Complex.smul_im,smul_eq_mul,mul_one,mul_zero]
  rw [he] at hp
  exact hp

theorem body_axis_mem {x : ℝ} (hx : 0 ≤ x) (hxu : x ≤ planarRadius A 0) : (⟨x,0⟩ : ℂ) ∈ C.body.carrier := by
  let t := x/planarRadius A 0
  have ht0 : 0 ≤ t := div_nonneg hx (C.radius_pos 0).le
  have ht1 : t ≤ 1 := (div_le_one (C.radius_pos 0)).mpr hxu
  have hp := C.body.convex C.body.zero_mem C.body_head_mem (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
  have he : (1-t) • (0 : ℂ)+t • (⟨planarRadius A 0,0⟩ : ℂ) = (⟨x,0⟩ : ℂ) := by
    apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,Complex.zero_re,Complex.zero_im,
      smul_eq_mul,mul_zero,zero_add]
    exact div_mul_cancel₀ x (C.radius_pos 0).ne'
  rwa [he] at hp

theorem body_terminal_segment_mem {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (⟨planarEpsilon A*y,y⟩ : ℂ) ∈ C.body.carrier := by
  have hp := C.body.convex C.body.zero_mem C.body_terminal_mem (sub_nonneg.mpr hy1) hy (by ring : (1-y)+y=1)
  have he : (1-y) • (0 : ℂ)+y • (⟨planarEpsilon A,1⟩ : ℂ) = (⟨planarEpsilon A*y,y⟩ : ℂ) := by
    apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,Complex.zero_re,Complex.zero_im,
      smul_eq_mul,mul_zero,zero_add,mul_one] <;> ring
  rwa [he] at hp

theorem body_in_terminal_wedge {v : ℂ} (hv : v ∈ C.body.carrier) : planarEpsilon A*v.im ≤ v.re := by
  have hh := C.body_linear_upper (⟨-1,planarEpsilon A⟩ : ℂ) 0 le_rfl (fun θ ht => by
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2.trans_lt C.angle_lt⟩
    have htangent := Real.strictMonoOn_tan.monotoneOn
      (show θ ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith [ht.1,Real.pi_pos],ht.2.trans_lt C.angle_lt⟩)
      (Real.arctan_mem_Ioo (planarEpsilon A)⁻¹) ht.2
    rw [Real.tan_arctan] at htangent
    have hratio : Real.sin θ/Real.cos θ ≤ 1/planarEpsilon A := by
      simpa only [Real.tan_eq_sin_div_cos,one_div] using htangent
    have hw := (div_le_div_iff₀ hc C.epsilon_pos).mp hratio
    have hm := mul_le_mul_of_nonneg_left hw (C.radius_pos θ).le
    simp only [complex_inner_coordinates,polarArc,polarUnit,Complex.smul_re,Complex.smul_im,smul_eq_mul,neg_one_mul]
    nlinarith only [hm]) v hv
  simp only [complex_inner_coordinates,neg_one_mul] at hh
  linarith

end
end StrongSilver.PlanarBoundaryCertificate
