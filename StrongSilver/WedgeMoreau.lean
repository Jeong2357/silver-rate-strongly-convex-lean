-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConePlaneRows
import StrongSilver.WedgeInvariance
import StrongSilver.MoreauFirm

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000

def WedgeRayRadial (P : Moreau.Epigraph ℂ) (c s : ℝ) : Prop :=
  ∀ n ∈ coneRays c s, ∀ t : ℝ, 0 ≤ t → ∃ p g : ℝ,
    Moreau.proximal P (t • n) = p • n ∧ Moreau.gradient P (t • n) = g • n

theorem wedge_moreau_invariant (P : Moreau.Epigraph ℂ) {c s : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c) (hu : c^2+s^2 = 1) (hrad : WedgeRayRadial P c s)
    {x : ℂ} (hx : x ∈ wedgeCone c s) :
    Moreau.proximal P x ∈ wedgeCone c s ∧ Moreau.gradient P x ∈ wedgeCone c s := by
  have hupper (t : ℝ) (ht : 0 ≤ t) := hrad (wedgeUpper c s) (by simp only [coneRays,List.mem_cons,true_or,eq_self]) t ht
  have hlower (t : ℝ) (ht : 0 ≤ t) := hrad (wedgeLower c s) (by simp [coneRays]) t ht
  constructor
  · apply wedge_firm_invariant hc hs hsc hu (Moreau.proximal P) (Moreau.proximal_firm P) _ _ hx
    · intro t ht; obtain ⟨p,g,hp,hg⟩ := hupper t ht; exact ⟨p,hp⟩
    · intro t ht; obtain ⟨p,g,hp,hg⟩ := hlower t ht; exact ⟨p,hp⟩
  · apply wedge_firm_invariant hc hs hsc hu (Moreau.gradient P) (Moreau.gradient_firm P) _ _ hx
    · intro t ht; obtain ⟨p,g,hp,hg⟩ := hupper t ht; exact ⟨g,hg⟩
    · intro t ht; obtain ⟨p,g,hp,hg⟩ := hlower t ht; exact ⟨g,hg⟩

theorem wedge_physical_normal_orthogonal (P : Moreau.Epigraph ℂ) (μ : ℝ) {c s : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c) (hu : c^2+s^2 = 1) (hrad : WedgeRayRadial P c s)
    {x q : ℂ} (hx : x ∈ wedgeCone c s) (hq : OutwardNormal (wedgeCone c s) x q) :
    inner ℝ q (stronglyConvexGradient μ (Moreau.gradient P) x) = 0 := by
  have hupper (t : ℝ) (ht : 0 ≤ t) : ∃ g : ℝ, Moreau.gradient P (t • wedgeUpper c s) = g • wedgeUpper c s := by
    obtain ⟨p,g,hp,hg⟩ := hrad (wedgeUpper c s) (by simp [coneRays]) t ht
    exact ⟨g,hg⟩
  have hlower (t : ℝ) (ht : 0 ≤ t) : ∃ g : ℝ, Moreau.gradient P (t • wedgeLower c s) = g • wedgeLower c s := by
    obtain ⟨p,g,hp,hg⟩ := hrad (wedgeLower c s) (by simp [coneRays]) t ht
    exact ⟨g,hg⟩
  apply linearCone_normal_orthogonal (wedgeForm c s) hx _ hq
  intro i hi
  have hf := wedge_active_face_tangent hc hs hsc hu (Moreau.gradient P) hupper hlower hx i hi
  change inner ℝ (wedgeInward c s i) x = 0 at hi
  change inner ℝ (wedgeInward c s i) (Moreau.gradient P x) = 0 at hf
  change inner ℝ (wedgeInward c s i) (stronglyConvexGradient μ (Moreau.gradient P) x) = 0
  simp only [stronglyConvexGradient,inner_add_right,real_inner_smul_right,hi,hf,mul_zero,add_zero]

end
end StrongSilver
