-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarDomainTrajectory

namespace StrongSilver.PlanarBoundaryCertificate
open Set Real Complex
noncomputable section
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C
set_option maxHeartbeats 1000000

theorem graphSlope_nonnegative (x : ℝ) : 0 ≤ C.graphSlope x := by
  by_cases hl : x ≤ C.left
  · rw [C.graphSlope_left hl]; exact div_nonneg zero_le_one C.epsilon_pos.le
  by_cases hr : C.right ≤ x
  · rw [C.graphSlope_right hr]; exact C.centralSlope_nonnegative C.right
  · rw [C.graphSlope_on_interval ⟨le_of_not_ge hl,le_of_not_ge hr⟩]
    exact C.centralSlope_nonnegative x

theorem graph_monotone : Monotone C.graph := by
  apply monotone_of_deriv_nonneg (fun x => (C.graph_hasDerivAt x).differentiableAt)
  intro x
  rw [(C.graph_hasDerivAt x).deriv]
  exact C.graphSlope_nonnegative x

theorem graph_in_terminal_wedge (x : ℝ) : C.graph x ≤ x/planarEpsilon A := by
  have hh := linearConcaveExtension_le_tangent C.left_lt_right.le
    (fun s hs x hx => concave_tangent_upper C.central_concave (fun t ht => C.central_hasDerivWithinAt ht) hs hx)
    C.centralSlope_antitone x (show C.left ∈ Icc C.left C.right from ⟨le_rfl,C.left_lt_right.le⟩)
  change C.graph x ≤ tangentLine C.centralGraph C.centralSlope C.left x at hh
  rw [tangentLine,C.central_left_value,C.central_left_slope,C.left_eq_epsilon] at hh
  have he : 1+(1/planarEpsilon A)*(x-planarEpsilon A) = x/planarEpsilon A := by
    field_simp [C.epsilon_pos.ne']
    <;> ring
  rwa [he] at hh

theorem domain_in_terminal_wedge {z : ℂ} (hz : z ∈ C.domain) : planarEpsilon A*z.im ≤ z.re := by
  have hu : z.im ≤ z.re/planarEpsilon A := hz.2.2.trans (C.graph_in_terminal_wedge z.re)
  have hh := (le_div_iff₀ C.epsilon_pos).mp hu
  nlinarith only [hh]

theorem domain_height_before_head {z : ℂ} (hz : z ∈ C.domain) (hx : z.re ≤ C.right) : z.im ≤ C.J 0 := by
  have hh := hz.2.2.trans (C.graph_monotone hx)
  rwa [C.graph_right_formula (le_refl C.right),sub_self,mul_zero,add_zero] at hh

theorem arc_im_monotone : MonotoneOn (fun θ => (polarArc (planarRadius A) θ).im)
    (Icc (0 : ℝ) (planarTerminalAngle A)) := by
  have hd (θ : ℝ) (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
      HasDerivAt (fun θ => (polarArc (planarRadius A) θ).im)
        (planarRadius A θ*(Real.cos θ-planarSlope A θ*Real.sin θ)) θ := by
    have h := (C.radius_hasDerivAt ht).mul (Real.hasDerivAt_sin θ)
    convert! h using 1
    · funext t
      simp only [polarArc,polarUnit,Complex.smul_im,smul_eq_mul,Pi.mul_apply]
    · ring
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun θ ht => (hd θ ht).continuousAt.continuousWithinAt)
    (fun θ ht => (hd θ (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro θ ht
  have ht0 := interior_subset ht
  rw [(hd θ ht0).deriv]
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht0.1,Real.pi_pos],ht0.2.trans_lt C.angle_lt⟩
  have hk := (smoothPlanarSlope_bounds C.scale_pos ht0.1 (ht0.2.trans_lt C.angle_lt)).2.2
  change 2*planarSlope A θ*Real.sin θ ≤ Real.cos θ at hk
  apply mul_nonneg (C.radius_pos θ).le
  nlinarith only [hc,hk]

theorem arc_terminal : polarArc (planarRadius A) (planarTerminalAngle A) = (⟨planarEpsilon A,1⟩ : ℂ) := by
  have hh := C.curve_terminal
  rwa [curve,planarBoundaryCurve_terminal C.terminal] at hh

theorem body_im_upper {v : ℂ} (hv : v ∈ C.body.carrier) : v.im ≤ 1 := by
  have hh := C.body_linear_upper (⟨0,1⟩ : ℂ) 1 zero_le_one (fun θ ht => by
    have hy := C.arc_im_monotone ht ⟨C.angle_pos.le,le_rfl⟩ ht.2
    change (polarArc (planarRadius A) θ).im ≤ (polarArc (planarRadius A) (planarTerminalAngle A)).im at hy
    rw [C.arc_terminal] at hy
    simpa only [complex_inner_coordinates,zero_mul,one_mul,zero_add] using hy) v hv
  simpa only [complex_inner_coordinates,zero_mul,one_mul,zero_add] using hh

/-- Both coordinates of the Moreau proximal residual are nonnegative in the domain. -/
theorem projection_residual_nonnegative {z : ℂ} (hz : z ∈ C.domain) :
    0 ≤ (z-C.body.projection z).re ∧ 0 ≤ (z-C.body.projection z).im := by
  let v := C.body.projection z
  have hv : v ∈ C.body.carrier := C.body.projection_mem z
  have hvy := C.body_im_nonnegative hv
  have hvx := C.body_re_nonnegative hv
  have hy : 0 ≤ z.im-v.im := by
    have hn := C.body.projection_normal z (⟨v.re,0⟩ : ℂ) (C.body_axis_mem hvx (C.body_re_upper hv))
    change inner ℝ (z-v) ((⟨v.re,0⟩ : ℂ)-v) ≤ 0 at hn
    simp only [complex_inner_coordinates,Complex.sub_re,Complex.sub_im,sub_self,mul_zero,zero_add,zero_sub] at hn
    by_cases he : v.im = 0
    · rw [he,sub_zero]; exact hz.2.1
    · have hp : 0 < v.im := lt_of_le_of_ne hvy (Ne.symm he)
      nlinarith only [hn,hp]
  have hx : 0 ≤ z.re-v.re := by
    have hn := C.body.projection_normal z (⟨planarEpsilon A*v.im,v.im⟩ : ℂ)
      (C.body_terminal_segment_mem hvy (C.body_im_upper hv))
    change inner ℝ (z-v) ((⟨planarEpsilon A*v.im,v.im⟩ : ℂ)-v) ≤ 0 at hn
    simp only [complex_inner_coordinates,Complex.sub_re,Complex.sub_im,sub_self,mul_zero,add_zero] at hn
    have hw := C.body_in_terminal_wedge hv
    rcases lt_or_eq_of_le hw with hlt | he
    · nlinarith only [hn,hlt]
    · have hwz := C.domain_in_terminal_wedge hz
      have hm := mul_nonneg C.epsilon_pos.le hy
      nlinarith only [he,hwz,hm]
  exact ⟨hx,hy⟩

end
end StrongSilver.PlanarBoundaryCertificate
