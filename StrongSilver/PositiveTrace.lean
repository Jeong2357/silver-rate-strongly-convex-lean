-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.EuclideanPath

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1400000

/-- A concrete positive finite-dimensional GD witness, including the full
schedule, source gate, directional bounds and an actual last-iterate ratio.
All objectives are supplied by SupportedPath.realize. -/
structure PositiveTrace (μ : ℝ) (h : List ℝ) (η M G r : ℝ) where
  dimension : ℕ
  length : ℕ
  path : SupportedPath (Space dimension) μ length
  steps_eq : List.ofFn path.steps = h
  nonzero : path.x 0 ≠ 0
  positive : path.family.PositiveAt (path.x 0)
  gate : path.family.Gate (path.x 0) η
  projections : ∀ i, |inner ℝ (unitDirection (path.x 0)) (path.family.z i)| ≤ M*‖path.x 0‖ ∧
    |inner ℝ (unitDirection (path.x 0)) (path.family.g i)| ≤ G*‖path.x 0‖
  ratio : r ≤ ‖path.x (Fin.last length)‖^2/‖path.x 0‖^2

namespace PositiveTrace
variable {μ η M G r : ℝ} {h : List ℝ}

def ofPath {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} (P : SupportedPath V μ n) (hs : List.ofFn P.steps = h) (hNZ : P.x 0 ≠ 0)
    (hp : P.family.PositiveAt (P.x 0)) (hg : P.family.Gate (P.x 0) η)
    (hb : ∀ i, |inner ℝ (unitDirection (P.x 0)) (P.family.z i)| ≤ M*‖P.x 0‖ ∧
      |inner ℝ (unitDirection (P.x 0)) (P.family.g i)| ≤ G*‖P.x 0‖)
    (hr : r ≤ ‖P.x (Fin.last n)‖^2/‖P.x 0‖^2) : PositiveTrace μ h η M G r := by
  let d := Classical.choose (exists_euclidean_isometry hNZ)
  have hT : Nonempty (V ≃ₗᵢ[ℝ] Space d) := Classical.choose_spec (exists_euclidean_isometry hNZ)
  let T := Classical.choice hT
  let Q := P.isometric T
  exact {
    dimension := d
    length := n
    path := Q
    steps_eq := hs
    nonzero := P.isometric_ne_zero T hNZ
    positive := P.isometric_positive T hp
    gate := P.isometric_gate T hg
    projections := P.isometric_projections T hb
    ratio := by
      change r ≤ ‖T (P.x (Fin.last n))‖^2/‖T (P.x 0)‖^2
      simpa only [T.norm_map] using hr
  }

def weaken (W : PositiveTrace μ h η M G r) {η' M' G' r' : ℝ}
    (hη : η' ≤ η) (hM : M ≤ M') (hG : G ≤ G') (hr : r' ≤ r) : PositiveTrace μ h η' M' G' r' where
  dimension := W.dimension
  length := W.length
  path := W.path
  steps_eq := W.steps_eq
  nonzero := W.nonzero
  positive := W.positive
  gate := W.path.family.gate_below W.positive.2 W.gate hη
  projections := by
    intro i
    exact ⟨(W.projections i).1.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _)),
      (W.projections i).2.trans (mul_le_mul_of_nonneg_right hG (norm_nonneg _))⟩
  ratio := hr.trans W.ratio

theorem distance_lower (W : PositiveTrace μ h η M G r) {κ : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) : ENNReal.ofReal r ≤ D κ h := by
  have hh := (ENNReal.ofReal_le_ofReal W.ratio).trans (W.path.distance_lower hκ hμ hμ1 W.nonzero)
  simpa only [W.steps_eq] using hh

theorem stable_ratio_le_one (W : PositiveTrace μ h η M G r) {κ : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) (hD : D κ h ≤ 1) : r ≤ 1 := by
  by_cases hr : 0 ≤ r
  · have hh := ENNReal.toReal_mono ENNReal.one_ne_top ((W.distance_lower hκ hμ hμ1).trans hD)
    simpa only [ENNReal.toReal_ofReal hr,ENNReal.toReal_one] using hh
  · exact (le_of_not_ge hr).trans zero_le_one

end PositiveTrace
end
end StrongSilver
