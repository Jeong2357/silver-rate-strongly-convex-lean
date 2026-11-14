-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PositiveTrace
import StrongSilver.FourPhaseSuffixBounds

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

/-- A finite Euclidean positive trace that also carries the retained
scale and height inequalities (4.18). This lets successive groups change
the dimension while preserving the actual original trajectory word. -/
structure FourPhaseTrace (μ : ℝ) (h : List ℝ) (H Z η M G r : ℝ)
    extends PositiveTrace μ h η M G r where
  suffix_bounds : FourPhaseSuffixBounds path.family (path.x 0) H Z

namespace FourPhaseTrace

def ofPath {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {μ H Z η M G r : ℝ} {h : List ℝ} {n : ℕ} (P : SupportedPath V μ n)
    (hs : List.ofFn P.steps = h) (B : FourPhaseSuffixBounds P.family (P.x 0) H Z)
    (hg : P.family.Gate (P.x 0) η)
    (hb : ∀ i, |inner ℝ (unitDirection (P.x 0)) (P.family.z i)| ≤ M*‖P.x 0‖ ∧
      |inner ℝ (unitDirection (P.x 0)) (P.family.g i)| ≤ G*‖P.x 0‖)
    (hr : r ≤ ‖P.x (Fin.last n)‖^2/‖P.x 0‖^2) : FourPhaseTrace μ h H Z η M G r := by
  let d := Classical.choose (exists_euclidean_isometry B.source_nonzero)
  have hT : Nonempty (V ≃ₗᵢ[ℝ] Space d) := Classical.choose_spec (exists_euclidean_isometry B.source_nonzero)
  let T := Classical.choice hT
  let Q := P.isometric T
  have hQ : FourPhaseSuffixBounds Q.family (Q.x 0) H Z :=
    B.transport T.toLinearMap (by norm_num : (0:ℝ) < 1) (fun x y => by
      change inner ℝ (T x) (T y) = 1*inner ℝ x y
      rw [T.inner_map_map,one_mul])
  exact {
    dimension := d
    length := n
    path := Q
    steps_eq := hs
    nonzero := P.isometric_ne_zero T B.source_nonzero
    positive := P.isometric_positive T B.positive_at
    gate := P.isometric_gate T hg
    projections := P.isometric_projections T hb
    ratio := by
      change r ≤ ‖T (P.x (Fin.last n))‖^2/‖T (P.x 0)‖^2
      simpa only [T.norm_map] using hr
    suffix_bounds := hQ
  }

end FourPhaseTrace
end
end StrongSilver
