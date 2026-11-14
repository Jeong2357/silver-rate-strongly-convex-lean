-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompactSupport
import StrongSilver.StrongMoreau

namespace StrongSilver.CompactConvexBody
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem exists_projection (K : CompactConvexBody V) (x : V) :
    ∃ v ∈ K.carrier, ∀ w ∈ K.carrier, ‖x-v‖ ≤ ‖x-w‖ :=
  K.compact.exists_isMinOn ⟨0,K.zero_mem⟩ (continuous_const.sub continuous_id).norm.continuousOn

def projection (K : CompactConvexBody V) (x : V) : V := (K.exists_projection x).choose

theorem projection_mem (K : CompactConvexBody V) (x : V) : K.projection x ∈ K.carrier :=
  (K.exists_projection x).choose_spec.1

theorem projection_min (K : CompactConvexBody V) (x w : V) (hw : w ∈ K.carrier) :
    ‖x-K.projection x‖ ≤ ‖x-w‖ := (K.exists_projection x).choose_spec.2 w hw

theorem projection_normal (K : CompactConvexBody V) (x w : V) (hw : w ∈ K.carrier) :
    inner ℝ (x-K.projection x) (w-K.projection x) ≤ 0 := by
  apply (norm_eq_iInf_iff_real_inner_le_zero K.convex (K.projection_mem x)).mp _ w hw
  letI : Nonempty K.carrier := ⟨⟨0,K.zero_mem⟩⟩
  apply le_antisymm
  · exact le_ciInf (fun w => K.projection_min x w w.property)
  · have hb : BddBelow (Set.range (fun w : K.carrier => ‖x-(w : V)‖)) :=
      ⟨(0 : ℝ),by rintro z ⟨w,rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hb ⟨K.projection x,K.projection_mem x⟩

theorem supportValue_projection_residual (K : CompactConvexBody V) (x : V) :
    K.supportValue (x-K.projection x) = inner ℝ (K.projection x) (x-K.projection x) := by
  apply le_antisymm
  · apply (K.supportValue_le _ _).mpr
    intro w hw
    have hh := K.projection_normal x w hw
    rw [inner_sub_right] at hh
    have he := real_inner_comm (x-K.projection x) (K.projection x)
    linarith only [hh,he]
  · simpa only [real_inner_comm] using K.inner_le_supportValue (x-K.projection x) (K.projection x) (K.projection_mem x)

theorem supportEpigraph_projection_supports (K : CompactConvexBody V) (x : V) :
    Moreau.Supports K.supportEpigraph (x-K.projection x)
      (K.supportValue (x-K.projection x)) (K.projection x) := by
  refine ⟨(show K.supportValue (x-K.projection x) ≤ K.supportValue (x-K.projection x) from le_rfl),fun q hq => ?_⟩
  change K.supportValue (x-K.projection x)+inner ℝ (K.projection x) (q.1-(x-K.projection x)) ≤ q.2
  rw [K.supportValue_projection_residual]
  simp only [inner_sub_right]
  have hinner : inner ℝ (K.projection x) q.1 ≤ K.supportValue q.1 := by
    simpa only [real_inner_comm] using K.inner_le_supportValue q.1 (K.projection x) (K.projection_mem x)
  change K.supportValue q.1 ≤ q.2 at hq
  linarith

variable [ProperSpace V]

/-- The gradient of the Moreau envelope of the support function is the metric projection. -/
theorem support_envelope_gradient (K : CompactConvexBody V) (x : V) :
    Moreau.gradient K.supportEpigraph x = K.projection x := by
  have hi := (Moreau.envelope_interpolates K.supportEpigraph (x-K.projection x) (K.projection x)
    (K.supportValue (x-K.projection x)) (K.supportEpigraph_projection_supports x)).1
  simpa only [sub_add_cancel] using hi

theorem support_projection_lipschitz (K : CompactConvexBody V) (x y : V) :
    ‖K.projection x-K.projection y‖ ≤ ‖x-y‖ := by
  rw [← K.support_envelope_gradient x,← K.support_envelope_gradient y]
  exact Moreau.gradient_lipschitz _ x y

theorem support_strong_admissible {κ μ : ℝ} (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1)
    (K : CompactConvexBody V) :
    Admissible κ (stronglyConvexObjective μ (Moreau.envelope K.supportEpigraph))
      (fun x => μ • x+(1-μ) • K.projection x) := by
  have hh := moreau_admissible_curvature hκ hμ hμ1 K.supportEpigraph
  change Admissible κ (stronglyConvexObjective μ (Moreau.envelope K.supportEpigraph))
    (fun x => μ • x+(1-μ) • Moreau.gradient K.supportEpigraph x) at hh
  simp_rw [K.support_envelope_gradient] at hh
  exact hh

end
end StrongSilver.CompactConvexBody
