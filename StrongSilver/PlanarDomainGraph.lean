-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarBoundaryCertificate
import StrongSilver.IntervalCurveGraph
import StrongSilver.DifferentiableExtrapolation
import StrongSilver.SubgraphDomain

namespace StrongSilver.PlanarBoundaryCertificate
open Set Real Complex
noncomputable section
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C
set_option maxHeartbeats 1000000

def xCoord (θ : ℝ) : ℝ := (C.curve θ).re
def yCoord (θ : ℝ) : ℝ := (C.curve θ).im
def left : ℝ := C.xCoord (planarTerminalAngle A)
def right : ℝ := C.xCoord 0

theorem x_continuousOn : ContinuousOn C.xCoord (Icc (0 : ℝ) (planarTerminalAngle A)) :=
  Complex.continuous_re.comp_continuousOn C.curve_continuousOn
theorem y_continuousOn : ContinuousOn C.yCoord (Icc (0 : ℝ) (planarTerminalAngle A)) :=
  Complex.continuous_im.comp_continuousOn C.curve_continuousOn

def inverse (x : ℝ) : ℝ := intervalGraphInverse C.angle_pos.le C.x_continuousOn C.x_strictAnti x
def centralGraph : ℝ → ℝ := intervalCurveGraph C.angle_pos.le C.x_continuousOn C.x_strictAnti
def centralSlope (x : ℝ) : ℝ := planarFieldSlope C.field (C.inverse x)

theorem inverse_mem (x : ℝ) : C.inverse x ∈ Icc (0 : ℝ) (planarTerminalAngle A) :=
  intervalGraphInverse_mem C.angle_pos.le C.x_continuousOn C.x_strictAnti x

theorem field_slope_strictMono : StrictMonoOn (planarFieldSlope C.field) (Icc (0 : ℝ) (planarTerminalAngle A)) := by
  apply planarFieldSlope_strictMonoOn (fun θ ht => (C.field_coordinates ht).1)
  intro θ ht
  obtain ⟨t,htn,hcurve⟩ := C.curve_hasDerivWithinAt ht
  have hd := planarBoundaryField_hasDerivWithinAt hcurve (C.radius_hasDerivAt ht).hasDerivWithinAt
  exact ⟨_,hd,planarBoundaryField_turning_pos C.mu_nonnegative C.mu_lt_one (C.radius_pos θ)
    (C.slope_pos ht) (C.nonnegative θ ht)⟩

theorem central_hasDerivWithinAt {x : ℝ} (hx : x ∈ Icc C.left C.right) :
    HasDerivWithinAt C.centralGraph (C.centralSlope x) (Icc C.left C.right) x := by
  have hi := C.inverse_mem x
  obtain ⟨t,htn,hcurve⟩ := C.curve_hasDerivWithinAt hi
  exact intervalCurveGraph_hasDerivWithinAt C.angle_pos.le C.x_continuousOn C.x_strictAnti hx
    htn.ne (C.field_coordinates hi).1.ne' hcurve

theorem centralSlope_antitone : AntitoneOn C.centralSlope (Icc C.left C.right) := by
  intro x hx y hy hxy
  have hi := intervalGraphInverse_antitoneOn C.angle_pos.le C.x_continuousOn C.x_strictAnti hx hy hxy
  exact C.field_slope_strictMono.monotoneOn (C.inverse_mem y) (C.inverse_mem x) hi

theorem central_concave : ConcaveOn ℝ (Icc C.left C.right) C.centralGraph :=
  intervalCurveGraph_concave C.angle_pos.le C.x_continuousOn C.x_strictAnti C.y_continuousOn
    (fun θ ht => (C.field_coordinates ht).1) (fun θ ht => C.curve_hasDerivWithinAt ht) C.field_slope_strictMono.monotoneOn

theorem left_lt_right : C.left < C.right :=
  C.x_strictAnti ⟨le_rfl,C.angle_pos.le⟩ ⟨C.angle_pos.le,le_rfl⟩ C.angle_pos

def graph : ℝ → ℝ := linearConcaveExtension C.left C.right C.centralGraph C.centralSlope
def graphSlope : ℝ → ℝ := extensionSlope C.left C.right C.centralSlope

theorem graph_hasDerivAt (x : ℝ) : HasDerivAt C.graph (C.graphSlope x) x :=
  linearConcaveExtension_hasDerivAt C.left_lt_right (fun x hx => C.central_hasDerivWithinAt hx) x

theorem graph_continuous : Continuous C.graph :=
  linearConcaveExtension_continuous C.left_lt_right (fun x hx => C.central_hasDerivWithinAt hx)

theorem graph_concave : ConcaveOn ℝ univ C.graph :=
  linearConcaveExtension_concave C.left_lt_right.le
    (fun s hs x hx => concave_tangent_upper C.central_concave (fun t ht => C.central_hasDerivWithinAt ht) hs hx)
    C.centralSlope_antitone

theorem left_eq_epsilon : C.left = planarEpsilon A := by
  change (C.curve (planarTerminalAngle A)).re = _
  rw [C.curve_terminal]

theorem central_on_curve {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
    C.centralGraph (C.xCoord θ) = C.yCoord θ :=
  intervalCurveGraph_on_curve C.angle_pos.le C.x_continuousOn C.x_strictAnti ht

theorem graph_on_curve {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
    C.graph (C.xCoord θ) = C.yCoord θ := by
  have hx : C.xCoord θ ∈ Icc C.left C.right :=
    ⟨C.x_strictAnti.antitoneOn ht ⟨C.angle_pos.le,le_rfl⟩ ht.2,
      C.x_strictAnti.antitoneOn ⟨le_rfl,C.angle_pos.le⟩ ht ht.1⟩
  rw [graph,linearConcaveExtension_on_interval hx]
  exact C.central_on_curve ht

theorem field_terminal : C.field (planarTerminalAngle A) = (⟨planarEpsilon A,1⟩ : ℂ) := by
  have hh : C.field (planarTerminalAngle A) = C.curve (planarTerminalAngle A) := by
    simp only [field,curve,planarBoundaryField,planarBoundaryCurve,C.terminal,mul_zero,zero_div,zero_smul,add_zero]
  exact hh.trans C.curve_terminal

theorem central_left_value : C.centralGraph C.left = 1 := by
  have hh := C.central_on_curve ⟨C.angle_pos.le,le_rfl⟩
  change C.centralGraph C.left = (C.curve (planarTerminalAngle A)).im at hh
  rwa [C.curve_terminal] at hh

theorem central_left_slope : C.centralSlope C.left = 1/planarEpsilon A := by
  have hi := intervalGraphInverse_left_inverse C.angle_pos.le C.x_continuousOn C.x_strictAnti ⟨C.angle_pos.le,le_rfl⟩
  change C.inverse C.left = planarTerminalAngle A at hi
  rw [centralSlope,hi,planarFieldSlope,C.field_terminal]

theorem centralSlope_nonnegative (x : ℝ) : 0 ≤ C.centralSlope x :=
  div_nonneg (C.field_coordinates (C.inverse_mem x)).2 (C.field_coordinates (C.inverse_mem x)).1.le

theorem graph_left_formula {x : ℝ} (hx : x ≤ C.left) : C.graph x = x/planarEpsilon A := by
  rw [graph,linearConcaveExtension_left C.left_lt_right.le C.centralGraph C.centralSlope hx,
    tangentLine,C.central_left_value,C.central_left_slope,C.left_eq_epsilon]
  field_simp [C.epsilon_pos.ne']
  <;> ring

theorem graph_zero : C.graph 0 = 0 := by
  rw [C.graph_left_formula (by rw [C.left_eq_epsilon]; exact C.epsilon_pos.le),zero_div]

theorem graph_nonnegative {x : ℝ} (hx : 0 ≤ x) : 0 ≤ C.graph x := by
  by_cases hleft : x ≤ C.left
  · rw [C.graph_left_formula hleft]
    exact div_nonneg hx C.epsilon_pos.le
  by_cases hright : C.right ≤ x
  · rw [graph,linearConcaveExtension_right C.left_lt_right.le C.centralGraph C.centralSlope hright,tangentLine]
    have hy := C.central_on_curve (show (0 : ℝ) ∈ Icc (0 : ℝ) (planarTerminalAngle A) from ⟨le_rfl,C.angle_pos.le⟩)
    have hhead : 0 ≤ C.centralGraph C.right := by
      change C.centralGraph C.right = (C.curve 0).im at hy
      rw [hy]
      simpa only [curve,planarBoundaryCurve_head] using (C.head_y_ge_one.trans' zero_le_one)
    exact add_nonneg hhead (mul_nonneg (C.centralSlope_nonnegative C.right) (sub_nonneg.mpr hright))
  · have hxIcc : x ∈ Icc C.left C.right := ⟨le_of_not_ge hleft,le_of_not_ge hright⟩
    rw [graph,linearConcaveExtension_on_interval hxIcc]
    have hi := C.inverse_mem x
    have hy := C.y_antitone hi ⟨C.angle_pos.le,le_rfl⟩ hi.2
    change (C.curve (planarTerminalAngle A)).im ≤ (C.curve (C.inverse x)).im at hy
    rw [C.curve_terminal] at hy
    change 0 ≤ (C.curve (C.inverse x)).im
    exact zero_le_one.trans hy

def domain : Set ℂ := subgraphDomain C.graph

theorem domain_closed : IsClosed C.domain := subgraphDomain_closed C.graph_continuous
theorem domain_convex : Convex ℝ C.domain := by
  apply subgraphDomain_convex
  refine ⟨convex_Ici (0 : ℝ),fun x hx y hy a b ha hb hab => ?_⟩
  exact C.graph_concave.2 (mem_univ x) (mem_univ y) ha hb hab

theorem curve_mem_domain {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) : C.curve θ ∈ C.domain := by
  have hx := C.x_strictAnti.antitoneOn ht ⟨C.angle_pos.le,le_rfl⟩ ht.2
  have hy := C.y_antitone ht ⟨C.angle_pos.le,le_rfl⟩ ht.2
  change C.left ≤ C.xCoord θ at hx
  change (C.curve (planarTerminalAngle A)).im ≤ (C.curve θ).im at hy
  rw [C.left_eq_epsilon] at hx
  rw [C.curve_terminal] at hy
  exact ⟨C.epsilon_pos.le.trans hx,zero_le_one.trans hy,(C.graph_on_curve ht).ge⟩

end
end StrongSilver.PlanarBoundaryCertificate
