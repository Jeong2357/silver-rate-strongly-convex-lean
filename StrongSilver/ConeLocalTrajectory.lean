-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeAttachmentCompatibility
import StrongSilver.ConeBackwardPath
import StrongSilver.DoubleWedgeInvariance
import StrongSilver.BackwardPrefixNorm
import StrongSilver.RunSupportedPath

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1800000
variable {μ b V₀ M H η : ℝ}

namespace ConeConnectorParameters

def traceRadius (C : ConeConnectorParameters μ b V₀ M H η) (h : List ℝ) : ℝ :=
  Real.exp (inverseCharge μ h)*(C.U+(1-μ)*(2*C.a)*smallPositiveSum μ h)

theorem radial (C : ConeConnectorParameters μ b V₀ M H η) : WedgeRayRadial C.epigraph C.c C.s := by
  intro n hn t ht
  obtain ⟨p,g,hp,hg,hgr,hpg,hprox,hgrad⟩ := coneEpigraph_ray_data C.a_pos.le C.d_pos.le C.cos_pos.le
    C.sin_pos.le C.unit C.radius_pos C.delta_nonnegative C.radius hn t ht
  exact ⟨p,g,hprox,hgrad⟩

theorem gradient_bound (C : ConeConnectorParameters μ b V₀ M H η) (z : ℂ) :
    ‖Moreau.gradient C.epigraph z‖ ≤ 2*C.a := by
  have hdA : C.d ≤ C.a := by
    have hh := mul_le_mul_of_nonneg_left C.sin_le_one C.a_pos.le
    nlinarith only [hh,C.d_small,C.a_pos]
  exact Moreau.plane_envelope_gradient_bound _
    (fun p hp => by rw [conePlaneRows_intercept _ _ _ _ _ _ p hp]; exact C.delta_nonnegative)
    (by have := C.a_pos; positivity)
    (conePlaneRows_norm_bound C.a_pos.le C.d_pos.le C.radius_pos.le C.unit (by linarith) C.radius_bound) z

theorem source_norm (C : ConeConnectorParameters μ b V₀ M H η) : ‖(⟨C.U,0⟩ : ℂ)‖ = C.U := by
  change ‖(C.U : ℂ)‖ = C.U
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos C.U_pos]

end ConeConnectorParameters

structure ConeLocalCertificate (C : ConeConnectorParameters μ b V₀ M H η) (h : List ℝ) where
  x : ℂ
  run : iterate h (stronglyConvexGradient μ (Moreau.gradient C.epigraph)) x = (⟨C.U,0⟩ : ℂ)
  states : ∀ i : ℕ, i ≤ h.length →
    iterate (h.take i) (stronglyConvexGradient μ (Moreau.gradient C.epigraph)) x ∈
      wedgeCone C.c C.s ∪ oppositeSet (wedgeCone C.c C.s)
  norm_bound : ∀ i : ℕ, ‖iterate (h.take i) (stronglyConvexGradient μ (Moreau.gradient C.epigraph)) x‖ ≤ C.traceRadius h
  nonzero : x ≠ 0

theorem exists_cone_local_certificate {C : ConeConnectorParameters μ b V₀ M H η} (hμ : 0 < μ)
    (hμ1 : μ ≤ 1) (h : List ℝ) (hcritical : ∀ t ∈ h, 1-μ*t ≠ 0) :
    Nonempty (ConeLocalCertificate C h) := by
  have hdA : C.d ≤ C.a := by
    have hh := mul_le_mul_of_nonneg_left C.sin_le_one C.a_pos.le
    nlinarith only [hh,C.d_small,C.a_pos]
  have hUcone : (⟨C.U,0⟩ : ℂ) ∈ wedgeCone C.c C.s ∪ oppositeSet (wedgeCone C.c C.s) := by
    left
    apply (wedge_mem_iff _ _ _).mpr
    constructor <;> simp only [mul_zero,sub_zero,add_zero] <;> exact mul_nonneg C.sin_pos.le C.U_pos.le
  have hU0 : (⟨C.U,0⟩ : ℂ) ≠ 0 := by intro hh; have he := congrArg Complex.re hh; exact C.U_pos.ne' he
  obtain ⟨x,hrun,hstates,hnorm,hnz⟩ := cone_epigraph_backward_path C.a_pos C.d_pos.le C.cos_pos C.sin_pos
    C.sin_cos C.unit C.radius_pos C.radius C.delta_nonnegative hdA C.radius_bound hμ hμ1 h hcritical
    (⟨C.U,0⟩ : ℂ) hUcone hU0
  refine ⟨⟨x,hrun,hstates,?_,?_⟩⟩
  · intro i
    have hh := backward_norm_all_prefixes hμ hμ1 (by have := C.a_pos; positivity) (Moreau.gradient C.epigraph)
      (Moreau.gradient_inner_nonnegative C.epigraph) C.gradient_bound h hcritical x _ hrun i
    simpa only [ConeConnectorParameters.traceRadius,C.source_norm] using hh
  · simpa only [List.take_zero,iterate_nil] using hnz 0

namespace ConeLocalCertificate
variable {C : ConeConnectorParameters μ b V₀ M H η} {h : List ℝ}

def path (L : ConeLocalCertificate C h) : SupportedPath ℂ μ (h++[b]).length :=
  SupportedPath.ofRun C.epigraph μ (h++[b]) L.x

theorem path_end (L : ConeLocalCertificate C h) : L.path.x (Fin.last _) = (⟨0,V₀⟩ : ℂ) := by
  rw [path,SupportedPath.ofRun_end,iterate_append,L.run]
  exact C.connector_step.2.2

theorem path_steps (L : ConeLocalCertificate C h) : List.ofFn L.path.steps = h++[b] := List.ofFn_get _

theorem query_eq (L : ConeLocalCertificate C h) (i : Fin (h++[b]).length) :
    iterate ((h++[b]).take i.val) (stronglyConvexGradient μ (Moreau.gradient C.epigraph)) L.x =
      iterate (h.take i.val) (stronglyConvexGradient μ (Moreau.gradient C.epigraph)) L.x := by
  rw [List.take_append_of_le_length (by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega)]

theorem supports (L : ConeLocalCertificate C h) (i : Fin (h++[b]).length) :
    Moreau.Supports C.epigraph (L.path.family.z i) (L.path.family.d i) (L.path.family.g i) :=
  Moreau.minimizingPair_supports C.epigraph _

theorem proximal_classification (L : ConeLocalCertificate C h) (i : Fin (h++[b]).length) :
    L.path.family.z i ∈ wedgeCone C.c C.s ∪ oppositeSet (wedgeCone C.c C.s) ∨
      L.path.family.z i = (⟨C.X,C.d⟩ : ℂ) := by
  change Moreau.proximal C.epigraph (iterate ((h++[b]).take i.val) _ L.x) ∈ _ ∨ _
  rw [L.query_eq]
  by_cases hi : i.val < h.length
  · left
    exact double_wedge_proximal_invariant C.epigraph C.cos_pos C.sin_pos C.sin_cos C.unit C.radial
      (L.states i.val hi.le)
  · right
    change Moreau.proximal C.epigraph (iterate ((h++[b]).take i.val) _ L.x) = _
    rw [L.query_eq]
    have he : i.val = h.length := by
      have hh := i.isLt
      simp only [List.length_append,List.length_singleton] at hh
      omega
    rw [he,List.take_length,L.run,C.connector_step.1]

theorem proximal_norm (L : ConeLocalCertificate C h) (i : Fin (h++[b]).length) :
    ‖L.path.family.z i‖ ≤ C.traceRadius h := by
  change ‖Moreau.proximal C.epigraph (iterate ((h++[b]).take i.val) _ L.x)‖ ≤ _
  rw [L.query_eq]
  exact (Moreau.proximal_norm_le C.epigraph _).trans (L.norm_bound _)

theorem slope_norm (L : ConeLocalCertificate C h) (i : Fin (h++[b]).length) :
    ‖L.path.family.g i‖ ≤ 2*C.a := C.gradient_bound _

end ConeLocalCertificate
end
end StrongSilver
