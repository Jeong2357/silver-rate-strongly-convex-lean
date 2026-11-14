-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeAttachedPath
import StrongSilver.PlaneProjectionBounds

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1800000
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [ProperSpace (AttachmentSpace V ℂ)]

/-- A suffix-preserving two-cone connector with explicit constants, actual
supported trajectories, and absolute projection bounds in the new source
direction. The numerical constants are constructed in this theorem. -/
theorem two_cone_attachment {μ b V₀ M H η : ℝ} (hμ : 0 < μ) (hb : 2 ≤ b)
    (hq : μ*b < 1) (hV : 0 < V₀) (hM : 1 ≤ M) (hH : 0 ≤ H) (hη : 0 < η) (hη1 : η ≤ 1)
    (h : List ℝ) (hcritical : ∀ t ∈ h, 1-μ*t ≠ 0)
    {m : ℕ} (Q : SupportedPath V μ m) (f : V) (hf : inner ℝ f f = 1) (hY : Q.x 0 = V₀ • f)
    (hprox : ∀ j, |inner ℝ f (Q.family.z j)| ≤ M*V₀)
    (hslope : ∀ j, |inner ℝ f (Q.family.g j)| ≤ H)
    (hplus : Q.family.Gate (Q.x 0) η) (hminus : Q.family.Gate (Q.x 0) (-η)) :
    ∃ C : ConeConnectorParameters μ b V₀ M H η, ∃ n : ℕ,
      ∃ J : SupportedPath (AttachmentSpace V ℂ) μ n,
        J.x 0 ≠ 0 ∧ ‖J.x 0‖ ≤ C.traceRadius h ∧
        J.x (Fin.last n) = retainedMap (W := ℂ) (Q.x (Fin.last m)) ∧
        List.ofFn J.steps = (h++[b])++List.ofFn Q.steps ∧
        (∀ k, |inner ℝ (unitDirection (J.x 0)) (J.family.z k)| ≤ C.traceRadius h+M*V₀) ∧
        (∀ k, |inner ℝ (unitDirection (J.x 0)) (J.family.g k)| ≤ 2*C.a+H) := by
  obtain ⟨C⟩ := exists_cone_connector_parameters hμ hb hq hV hM hH hη hη1
  have hμ1 : μ ≤ 1 := by nlinarith only [hq,hb,hμ]
  obtain ⟨L⟩ := exists_cone_local_certificate (C := C) hμ hμ1 h hcritical
  obtain ⟨n,J,hsource,hend,hsteps,horigin⟩ := exists_cone_attached_path L Q f hf hY hV hη hH
    hprox hslope hplus hminus
  have hR : 0 ≤ C.traceRadius h := (norm_nonneg _).trans (L.norm_bound 0)
  have hMV : 0 ≤ M*V₀ := mul_nonneg (by linarith) hV.le
  refine ⟨C,n,J,?_,?_,hend,hsteps,?_,?_⟩
  · rw [hsource]
    exact plane_attachment_ne_zero hf L.nonzero
  · rw [hsource,plane_attachment_norm hf]
    simpa only [List.take_zero,iterate_nil] using L.norm_bound 0
  · intro k
    rw [hsource]
    rcases horigin k with ⟨i,hz,hg,hd⟩ | ⟨j,hz,hg,hd⟩
    · rw [hz]
      exact ((plane_local_projection hf L.nonzero _).trans (L.proximal_norm i)).trans (le_add_of_nonneg_right hMV)
    · rw [hz]
      exact ((plane_retained_projection hf L.nonzero _).trans (hprox j)).trans (le_add_of_nonneg_left hR)
  · intro k
    rw [hsource]
    rcases horigin k with ⟨i,hz,hg,hd⟩ | ⟨j,hz,hg,hd⟩
    · rw [hg]
      exact ((plane_local_projection hf L.nonzero _).trans (L.slope_norm i)).trans (le_add_of_nonneg_right hH)
    · rw [hg]
      exact ((plane_retained_projection hf L.nonzero _).trans (hslope j)).trans (le_add_of_nonneg_left (by have := C.a_pos; positivity))

end
end StrongSilver
