-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarHeadProjection

namespace StrongSilver.PlanarBoundaryCertificate
open Set Real Complex
noncomputable section
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C
set_option maxHeartbeats 1000000

def physical : ℂ → ℂ := stronglyConvexGradient μ (Moreau.gradient C.body.supportEpigraph)

theorem right_eq_head : C.right = planarRadius A 0+C.J 0/planarSlopeScale A := by
  change (planarBoundaryCurve (planarRadius A) (planarSlope A) C.J 0).re = _
  rw [planarBoundaryCurve_head,C.slope_zero]

theorem right_ge_radius : planarRadius A 0 ≤ C.right := by
  rw [C.right_eq_head]
  exact le_add_of_nonneg_right (div_nonneg (zero_le_one.trans C.head_y_ge_one) C.scale_pos.le)

theorem right_pos : 0 < C.right := (C.radius_pos 0).trans_le C.right_ge_radius

theorem central_right_value : C.centralGraph C.right = C.J 0 := by
  have hh := C.central_on_curve (show (0 : ℝ) ∈ Icc (0 : ℝ) (planarTerminalAngle A) from ⟨le_rfl,C.angle_pos.le⟩)
  change C.centralGraph C.right = (C.curve 0).im at hh
  simpa only [curve,planarBoundaryCurve_head] using hh

theorem field_head : C.field 0 = (⟨planarRadius A 0+μ*C.J 0/planarSlopeScale A,μ*C.J 0⟩ : ℂ) := by
  apply Complex.ext <;> simp only [field,planarBoundaryField,C.slope_zero,polarUnit,polarTangent,
    Real.cos_zero,Real.sin_zero,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul,
    neg_zero,mul_one,mul_zero,add_zero,zero_add]

theorem central_right_slope : C.centralSlope C.right = (μ*C.J 0)/(planarRadius A 0+μ*C.J 0/planarSlopeScale A) := by
  have hi := intervalGraphInverse_left_inverse C.angle_pos.le C.x_continuousOn C.x_strictAnti
    (show (0 : ℝ) ∈ Icc (0 : ℝ) (planarTerminalAngle A) from ⟨le_rfl,C.angle_pos.le⟩)
  change C.inverse C.right = 0 at hi
  rw [centralSlope,hi,planarFieldSlope,C.field_head]

theorem head_denominator_pos : 0 < planarRadius A 0+μ*C.J 0/planarSlopeScale A := by
  have hh := (C.field_coordinates (show (0 : ℝ) ∈ Icc (0 : ℝ) (planarTerminalAngle A) from ⟨le_rfl,C.angle_pos.le⟩)).1
  rwa [C.field_head] at hh

theorem right_slope_mul : C.centralSlope C.right*(planarRadius A 0+μ*C.J 0/planarSlopeScale A) = μ*C.J 0 := by
  rw [C.central_right_slope]
  exact div_mul_cancel₀ _ C.head_denominator_pos.ne'

theorem right_slope_le_scale : C.centralSlope C.right ≤ planarSlopeScale A := by
  rw [C.central_right_slope]
  apply (div_le_iff₀ C.head_denominator_pos).mpr
  have he : planarSlopeScale A*(planarRadius A 0+μ*C.J 0/planarSlopeScale A) =
      planarSlopeScale A*planarRadius A 0+μ*C.J 0 := by field_simp [C.scale_pos.ne'] <;> ring
  rw [he]
  exact le_add_of_nonneg_left (mul_nonneg C.scale_pos.le (C.radius_pos 0).le)

theorem graph_right_formula {x : ℝ} (hx : C.right ≤ x) :
    C.graph x = C.J 0+C.centralSlope C.right*(x-C.right) := by
  rw [graph,linearConcaveExtension_right C.left_lt_right.le C.centralGraph C.centralSlope hx,
    tangentLine,C.central_right_value]

theorem graphSlope_on_interval {x : ℝ} (hx : x ∈ Icc C.left C.right) : C.graphSlope x = C.centralSlope x := by
  simp only [graphSlope,extensionSlope,not_lt.mpr hx.1,not_lt.mpr hx.2,if_false]

theorem graphSlope_left {x : ℝ} (hx : x ≤ C.left) : C.graphSlope x = 1/planarEpsilon A := by
  rcases lt_or_eq_of_le hx with hlt | rfl
  · simp only [graphSlope,extensionSlope,hlt,if_true,C.central_left_slope]
  · rw [C.graphSlope_on_interval ⟨le_rfl,C.left_lt_right.le⟩,C.central_left_slope]

theorem graphSlope_right {x : ℝ} (hx : C.right ≤ x) : C.graphSlope x = C.centralSlope C.right := by
  rcases lt_or_eq_of_le hx with hlt | rfl
  · simp only [graphSlope,extensionSlope,not_lt.mpr (C.left_lt_right.le.trans hlt.le),if_false,hlt,if_true]
  · exact C.graphSlope_on_interval ⟨C.left_lt_right.le,le_rfl⟩

theorem right_graph_in_head_region {x : ℝ} (hx : C.right ≤ x) :
    C.graph x ≤ planarSlopeScale A*(x-planarRadius A 0) := by
  have hm := mul_le_mul_of_nonneg_right C.right_slope_le_scale (sub_nonneg.mpr hx)
  have hbase : C.J 0 = planarSlopeScale A*(C.right-planarRadius A 0) := by
    rw [C.right_eq_head]
    field_simp [C.scale_pos.ne']
    <;> ring
  rw [C.graph_right_formula hx]
  nlinarith only [hm,hbase]

theorem right_graph_projection {x : ℝ} (hx : C.right ≤ x) :
    C.body.projection (⟨x,C.graph x⟩ : ℂ) = (⟨planarRadius A 0,0⟩ : ℂ) :=
  C.projection_head_region (C.right_ge_radius.trans hx) (C.graph_nonnegative (C.right_pos.le.trans hx))
    (C.right_graph_in_head_region hx)

theorem left_graph_mem_body {x : ℝ} (hx : 0 ≤ x) (hxu : x ≤ C.left) :
    (⟨x,C.graph x⟩ : ℂ) ∈ C.body.carrier := by
  have hxε : x ≤ planarEpsilon A := hxu.trans_eq C.left_eq_epsilon
  have hp := C.body_terminal_segment_mem (div_nonneg hx C.epsilon_pos.le) ((div_le_one C.epsilon_pos).mpr hxε)
  have he : (⟨planarEpsilon A*(x/planarEpsilon A),x/planarEpsilon A⟩ : ℂ) = (⟨x,C.graph x⟩ : ℂ) := by
    apply Complex.ext
    · exact mul_div_cancel₀ x C.epsilon_pos.ne'
    · exact (C.graph_left_formula hxu).symm
  rwa [he] at hp

end
end StrongSilver.PlanarBoundaryCertificate
