-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SignedWedgeNormal

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000

theorem double_wedge_firm_invariant {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c)
    (hu : c^2+s^2 = 1) (F : ℂ → ℂ)
    (hfirm : ∀ x y, ‖F x-F y‖^2 ≤ inner ℝ (F x-F y) (x-y))
    (hrad : ∀ n ∈ coneRays c s, ∀ t : ℝ, 0 ≤ t → ∃ a : ℝ, F (t • n) = a • n)
    {x : ℂ} (hx : x ∈ wedgeCone c s ∪ oppositeSet (wedgeCone c s)) :
    F x ∈ wedgeCone c s ∪ oppositeSet (wedgeCone c s) := by
  have hinv : ∀ z ∈ wedgeCone c s, F z ∈ wedgeCone c s := fun z hz =>
    wedge_firm_invariant hc hs hsc hu F hfirm
      (fun t ht => hrad _ (by simp [coneRays]) t ht)
      (fun t ht => hrad _ (by simp [coneRays]) t ht) hz
  rcases hx with hx | hx
  · exact Or.inl (hinv x hx)
  · right
    have hnrad (n : ℂ) (hn : n ∈ coneRays c s) (t : ℝ) (ht : 0 ≤ t) :
        ∃ a : ℝ, negativeConjugate F (t • n) = a • n :=
      negativeConjugate_radial F n (hrad (-n) (coneRays_neg_mem hn)) t ht
    have hh := wedge_firm_invariant hc hs hsc hu (negativeConjugate F) (negativeConjugate_firm F hfirm)
      (fun t ht => hnrad _ (by simp [coneRays]) t ht)
      (fun t ht => hnrad _ (by simp [coneRays]) t ht) hx
    simpa only [oppositeSet,mem_setOf_eq,negativeConjugate,neg_neg] using hh

theorem double_wedge_proximal_invariant (P : Moreau.Epigraph ℂ) {c s : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c) (hu : c^2+s^2 = 1) (hrad : WedgeRayRadial P c s)
    {x : ℂ} (hx : x ∈ wedgeCone c s ∪ oppositeSet (wedgeCone c s)) :
    Moreau.proximal P x ∈ wedgeCone c s ∪ oppositeSet (wedgeCone c s) := by
  apply double_wedge_firm_invariant hc hs hsc hu (Moreau.proximal P) (Moreau.proximal_firm P) _ hx
  intro n hn t ht
  obtain ⟨p,g,hp,hg⟩ := hrad n hn t ht
  exact ⟨p,hp⟩

end
end StrongSilver
