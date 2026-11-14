-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportProjection
import StrongSilver.ScalarReconstruction

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

theorem Moreau.minimizingPair_eq_from_supports (P : Moreau.Epigraph V) (z g : V) (d : ℝ)
    (hs : Moreau.Supports P z d g) : Moreau.minimizingPair P (z+g) = (z,d) := by
  apply Moreau.minimizingPair_eq_of_supports
  have he : z+g-z = g := by abel
  rwa [he]

theorem CompactConvexBody.exact_proximal_values (K : CompactConvexBody V) (x : V) :
    Moreau.minimizingPair K.supportEpigraph x =
      (x-K.projection x,K.supportValue (x-K.projection x)) := by
  have hh := Moreau.minimizingPair_eq_from_supports K.supportEpigraph (x-K.projection x) (K.projection x)
    (K.supportValue (x-K.projection x)) (K.supportEpigraph_projection_supports x)
  simpa only [sub_add_cancel] using hh

theorem ScalarContraction.exact_proximal_values (S : ScalarContraction) (x : ℝ) :
    Moreau.minimizingPair S.epigraph x = (S.proximalMap x,S.potential (S.proximalMap x)) := by
  have hh := Moreau.minimizingPair_eq_from_supports S.epigraph (S.proximalMap x) (S.g x)
    (S.potential (S.proximalMap x)) (S.supports_proximal x)
  have he : S.proximalMap x+S.g x = x := by dsimp [ScalarContraction.proximalMap]; ring
  rwa [he] at hh

end
end StrongSilver
