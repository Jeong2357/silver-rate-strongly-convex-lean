-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WedgeMoreau
import StrongSilver.OppositeDomain

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000

theorem coneRays_neg_mem {c s : ℝ} {n : ℂ} (hn : n ∈ coneRays c s) : -n ∈ coneRays c s := by
  simp only [coneRays,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> simp [coneRays]

theorem negativeConjugate_radial (F : ℂ → ℂ) (n : ℂ)
    (hrad : ∀ t : ℝ, 0 ≤ t → ∃ a : ℝ, F (t • (-n)) = a • (-n))
    (t : ℝ) (ht : 0 ≤ t) : ∃ a : ℝ, negativeConjugate F (t • n) = a • n := by
  obtain ⟨a,ha⟩ := hrad t ht
  have he : -(t • n) = t • (-n) := by module
  refine ⟨a,?_⟩
  unfold negativeConjugate
  rw [he,ha]
  module

theorem wedge_strongified_normal_orthogonal {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c)
    (hu : c^2+s^2 = 1) (F : ℂ → ℂ) (μ : ℝ)
    (hupper : ∀ t : ℝ, 0 ≤ t → ∃ a : ℝ, F (t • wedgeUpper c s) = a • wedgeUpper c s)
    (hlower : ∀ t : ℝ, 0 ≤ t → ∃ a : ℝ, F (t • wedgeLower c s) = a • wedgeLower c s)
    {x q : ℂ} (hx : x ∈ wedgeCone c s) (hq : OutwardNormal (wedgeCone c s) x q) :
    inner ℝ q (stronglyConvexGradient μ F x) = 0 := by
  apply linearCone_normal_orthogonal (wedgeForm c s) hx _ hq
  intro i hi
  have hf := wedge_active_face_tangent hc hs hsc hu F hupper hlower hx i hi
  change inner ℝ (wedgeInward c s i) x = 0 at hi
  change inner ℝ (wedgeInward c s i) (F x) = 0 at hf
  change inner ℝ (wedgeInward c s i) (stronglyConvexGradient μ F x) = 0
  simp only [stronglyConvexGradient,inner_add_right,real_inner_smul_right,hi,hf,mul_zero,add_zero]

theorem wedge_opposite_physical_normal_orthogonal (P : Moreau.Epigraph ℂ) (μ : ℝ) {c s : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c) (hu : c^2+s^2 = 1) (hrad : WedgeRayRadial P c s)
    {x q : ℂ} (hx : x ∈ oppositeSet (wedgeCone c s))
    (hq : OutwardNormal (oppositeSet (wedgeCone c s)) x q) :
    inner ℝ q (stronglyConvexGradient μ (Moreau.gradient P) x) = 0 := by
  apply oppositeSet_normal_orthogonal (stronglyConvexGradient μ (Moreau.gradient P)) _ hx hq
  intro y hy v hv
  have hupper (t : ℝ) (ht : 0 ≤ t) : ∃ a : ℝ,
      negativeConjugate (Moreau.gradient P) (t • wedgeUpper c s) = a • wedgeUpper c s := by
    apply negativeConjugate_radial
    · intro u hu0
      obtain ⟨p,g,hp,hg⟩ := hrad (-wedgeUpper c s) (by simp [coneRays]) u hu0
      exact ⟨g,hg⟩
    · exact ht
  have hlower (t : ℝ) (ht : 0 ≤ t) : ∃ a : ℝ,
      negativeConjugate (Moreau.gradient P) (t • wedgeLower c s) = a • wedgeLower c s := by
    apply negativeConjugate_radial
    · intro u hu0
      obtain ⟨p,g,hp,hg⟩ := hrad (-wedgeLower c s) (by simp [coneRays]) u hu0
      exact ⟨g,hg⟩
    · exact ht
  have hh := wedge_strongified_normal_orthogonal hc hs hsc hu
    (negativeConjugate (Moreau.gradient P)) μ hupper hlower hy hv
  have he : negativeConjugate (stronglyConvexGradient μ (Moreau.gradient P)) y =
      stronglyConvexGradient μ (negativeConjugate (Moreau.gradient P)) y := by
    unfold negativeConjugate stronglyConvexGradient
    module
  rwa [he]

end
end StrongSilver
