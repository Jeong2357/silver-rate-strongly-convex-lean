-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarGraphInterfaces

namespace StrongSilver.PlanarBoundaryCertificate
open Set Real Complex
noncomputable section
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C
set_option maxHeartbeats 1000000

theorem physical_on_curve {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
    C.physical (C.curve θ) = C.field θ := C.field_is_actual_gradient ht

theorem central_graph_eq_curve {x : ℝ} (hx : x ∈ Icc C.left C.right) :
    C.curve (C.inverse x) = (⟨x,C.graph x⟩ : ℂ) := by
  have hre := intervalGraphInverse_right_inverse C.angle_pos.le C.x_continuousOn C.x_strictAnti hx
  change C.xCoord (C.inverse x) = x at hre
  have him := C.graph_on_curve (C.inverse_mem x)
  rw [hre] at him
  exact Complex.ext hre him.symm

theorem central_physical_tangent {x : ℝ} (hx : x ∈ Icc C.left C.right) :
    (C.physical (⟨x,C.graph x⟩ : ℂ)).im = C.graphSlope x*(C.physical (⟨x,C.graph x⟩ : ℂ)).re := by
  rw [← C.central_graph_eq_curve hx,C.physical_on_curve (C.inverse_mem x),C.graphSlope_on_interval hx]
  change (C.field (C.inverse x)).im =
    ((C.field (C.inverse x)).im/(C.field (C.inverse x)).re)*(C.field (C.inverse x)).re
  exact (div_mul_cancel₀ _ (C.field_coordinates (C.inverse_mem x)).1.ne').symm

theorem left_physical_tangent {x : ℝ} (hx : 0 ≤ x) (hxu : x ≤ C.left) :
    (C.physical (⟨x,C.graph x⟩ : ℂ)).im = C.graphSlope x*(C.physical (⟨x,C.graph x⟩ : ℂ)).re := by
  have hphys : C.physical (⟨x,C.graph x⟩ : ℂ) = (⟨x,C.graph x⟩ : ℂ) :=
    support_gradient_at_body_point (C.left_graph_mem_body hx hxu) μ
  rw [hphys,C.graphSlope_left hxu,C.graph_left_formula hxu]
  ring

theorem right_physical_tangent {x : ℝ} (hx : C.right ≤ x) :
    (C.physical (⟨x,C.graph x⟩ : ℂ)).im = C.graphSlope x*(C.physical (⟨x,C.graph x⟩ : ℂ)).re := by
  have hphys : C.physical (⟨x,C.graph x⟩ : ℂ) =
      μ • (⟨x,C.graph x⟩ : ℂ)+(1-μ) • (⟨planarRadius A 0,0⟩ : ℂ) := by
    unfold physical stronglyConvexGradient
    rw [C.body.support_envelope_gradient,C.right_graph_projection hx]
  rw [hphys,C.graphSlope_right hx]
  simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul,mul_zero,add_zero]
  have hden : μ*C.right+(1-μ)*planarRadius A 0 = planarRadius A 0+μ*C.J 0/planarSlopeScale A := by
    rw [C.right_eq_head]
    ring
  have hm := C.right_slope_mul
  rw [← hden] at hm
  rw [C.graph_right_formula hx]
  nlinarith only [hm]

theorem graph_physical_tangent {x : ℝ} (hx : 0 < x) :
    (C.physical (⟨x,C.graph x⟩ : ℂ)).im = C.graphSlope x*(C.physical (⟨x,C.graph x⟩ : ℂ)).re := by
  by_cases hleft : x ≤ C.left
  · exact C.left_physical_tangent hx.le hleft
  by_cases hright : C.right ≤ x
  · exact C.right_physical_tangent hright
  · exact C.central_physical_tangent ⟨le_of_not_ge hleft,le_of_not_ge hright⟩

/-- The concrete domain satisfies the normal orthogonality condition for the
actual Moreau-gradient field, including both straight extensions. -/
theorem domain_normal_orthogonal {z q : ℂ} (hz : z ∈ C.domain) (hq : OutwardNormal C.domain z q) :
    inner ℝ q (C.physical z) = 0 :=
  subgraph_normal_orthogonal (fun x hx => C.graph_nonnegative hx) C.graph_zero
    (fun x hx => C.graph_hasDerivAt x) C.physical C.physical_gradient_zero
    (fun x hx => C.axis_gradient_im hx) (fun x hx => C.graph_physical_tangent hx) hz hq

end
end StrongSilver.PlanarBoundaryCertificate
