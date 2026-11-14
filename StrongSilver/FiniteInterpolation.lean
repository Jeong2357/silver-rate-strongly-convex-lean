-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.MoreauExtended
import Mathlib.Analysis.Convex.Continuous

namespace StrongSilver.Moreau
open Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def planeMaximum (rows : List (E × ℝ)) (x : E) : ℝ :=
  rows.foldr (fun r v => max (inner ℝ r.1 x-r.2) v) 0

theorem planeMaximum_le (rows : List (E × ℝ)) (x : E) (a : ℝ) :
    planeMaximum rows x ≤ a ↔ 0 ≤ a ∧ ∀ r ∈ rows, inner ℝ r.1 x-r.2 ≤ a := by
  induction rows with
  | nil => simp [planeMaximum]
  | cons r rows ih =>
    simp only [planeMaximum, List.foldr_cons, max_le_iff] at *
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem planeMaximum_nonnegative (rows : List (E × ℝ)) (x : E) : 0 ≤ planeMaximum rows x :=
  ((planeMaximum_le rows x _).mp le_rfl).1

theorem plane_le_maximum (rows : List (E × ℝ)) (r : E × ℝ) (hr : r ∈ rows) (x : E) :
    inner ℝ r.1 x-r.2 ≤ planeMaximum rows x :=
  ((planeMaximum_le rows x _).mp le_rfl).2 r hr

theorem planeMaximum_continuous (rows : List (E × ℝ)) : Continuous (planeMaximum rows) := by
  induction rows with
  | nil => exact continuous_const
  | cons r rows ih =>
    change Continuous (fun x => max (inner ℝ r.1 x-r.2) (planeMaximum rows x))
    fun_prop

theorem planeMaximum_convex (rows : List (E × ℝ)) : ConvexOn ℝ univ (planeMaximum rows) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  change planeMaximum rows (a • x+b • y) ≤ a*planeMaximum rows x+b*planeMaximum rows y
  apply (planeMaximum_le _ _ _).mpr
  refine ⟨add_nonneg (mul_nonneg ha (planeMaximum_nonnegative _ _))
    (mul_nonneg hb (planeMaximum_nonnegative _ _)),fun r hr => ?_⟩
  have hx := mul_le_mul_of_nonneg_left (plane_le_maximum rows r hr x) ha
  have hy := mul_le_mul_of_nonneg_left (plane_le_maximum rows r hr y) hb
  simp only [inner_add_right, inner_smul_right, smul_eq_mul]
  have hc : (a+b)*r.2 = r.2 := by rw [hab,one_mul]
  nlinarith

theorem planeMaximum_zero (rows : List (E × ℝ)) (hc : ∀ r ∈ rows, 0 ≤ r.2) :
    planeMaximum rows 0 = 0 := by
  apply le_antisymm _ (planeMaximum_nonnegative _ _)
  apply (planeMaximum_le _ _ _).mpr
  exact ⟨le_rfl,fun r hr => by simpa using neg_nonpos.mpr (hc r hr)⟩

def finiteEpigraph (f : E → ℝ) (hc : Continuous f) (hv : ConvexOn ℝ univ f)
    (hn : ∀ x, 0 ≤ f x) (hz : f 0 = 0) : Epigraph E where
  carrier := {p | f p.1 ≤ p.2}
  closed := isClosed_le (hc.comp continuous_fst) continuous_snd
  convex := by simpa using hv.convex_epigraph
  nonnegative := fun p hp => (hn p.1).trans hp
  zero_mem := by simpa using hz.le
  upward := fun p hp s hs => hp.trans hs

def planeEpigraph (rows : List (E × ℝ)) (hc : ∀ r ∈ rows, 0 ≤ r.2) : Epigraph E :=
  finiteEpigraph (planeMaximum rows) (planeMaximum_continuous rows) (planeMaximum_convex rows)
    (planeMaximum_nonnegative rows) (planeMaximum_zero rows hc)

theorem active_plane_supports (rows : List (E × ℝ)) (hc : ∀ r ∈ rows, 0 ≤ r.2)
    (z g : E) (d : ℝ) (hd : 0 ≤ d) (hr : (g,inner ℝ g z-d) ∈ rows)
    (ht : ∀ r ∈ rows, inner ℝ r.1 z-r.2 ≤ d) :
    Supports (planeEpigraph rows hc) z d g := by
  refine ⟨(planeMaximum_le _ _ _).mpr ⟨hd,ht⟩,fun q hq => ?_⟩
  have hp := (plane_le_maximum rows (g,inner ℝ g z-d) hr q.1).trans hq
  simp only [inner_sub_right]
  dsimp at hp
  linarith

theorem active_plane_value (rows : List (E × ℝ)) (z g : E) (d : ℝ)
    (hd : 0 ≤ d) (hr : (g,inner ℝ g z-d) ∈ rows)
    (ht : ∀ r ∈ rows, inner ℝ r.1 z-r.2 ≤ d) : planeMaximum rows z = d := by
  apply le_antisymm ((planeMaximum_le _ _ _).mpr ⟨hd,ht⟩)
  simpa using plane_le_maximum rows (g,inner ℝ g z-d) hr z

/-- Replacing any admissible extended potential by finitely many supporting planes
preserves its values and subgradients at all prescribed data points. -/
theorem finite_plane_replacement (P : Potential E) (n : ℕ) (z g : Fin n → E)
    (hs : ∀ i, P.Subgradient (z i) (g i)) :
    ∃ f : E → ℝ, Continuous f ∧ ConvexOn ℝ univ f ∧ f 0=0 ∧ (∀ x, 0 ≤ f x) ∧
      ∀ i, f (z i)=(P.value (z i)).toReal ∧
        ∀ w, f (z i)+inner ℝ (g i) (w-z i) ≤ f w := by
  let d := fun i => (P.value (z i)).toReal
  let rows := List.ofFn (fun i => (g i,inner ℝ (g i) (z i)-d i))
  have hc (i : Fin n) : d i ≤ inner ℝ (g i) (z i) := by
    have h := (hs i).2 0 (by rw [P.zero]; exact ENNReal.zero_ne_top)
    simp only [P.zero, ENNReal.toReal_zero, zero_sub, inner_neg_right] at h
    dsimp [d]
    linarith
  have hr : ∀ r ∈ rows, 0 ≤ r.2 := by
    intro r h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact sub_nonneg.mpr (hc i)
  refine ⟨planeMaximum rows,planeMaximum_continuous rows,planeMaximum_convex rows,
    planeMaximum_zero rows hr,planeMaximum_nonnegative rows,fun i => ?_⟩
  have hri : (g i,inner ℝ (g i) (z i)-d i) ∈ rows := List.mem_ofFn.mpr ⟨i,rfl⟩
  have ht : ∀ r ∈ rows, inner ℝ r.1 (z i)-r.2 ≤ d i := by
    intro r h
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
    have hh := (hs j).2 (z i) (hs i).1
    simp only [inner_sub_right] at hh
    dsimp [d]
    linarith
  have he := active_plane_value rows (z i) (g i) (d i) ENNReal.toReal_nonneg hri ht
  refine ⟨he,fun w => ?_⟩
  rw [he,inner_sub_right]
  have h := plane_le_maximum rows (g i,inner ℝ (g i) (z i)-d i) hri w
  dsimp at h
  linarith

variable [ProperSpace E]

/-- Smooth convex interpolation of a finite set of compatible subgradient data.
This is an existence theorem for actual functions, with no interpolation oracle. -/
theorem finite_smooth_interpolation (n : ℕ) (z g : Fin n → E) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hc : ∀ i, d i ≤ inner ℝ (g i) (z i))
    (hi : ∀ i j, d i + inner ℝ (g i) (z j-z i) ≤ d j) :
    ∃ f : E → ℝ, ∃ grad : E → E,
      ConvexOn ℝ univ f ∧ (∀ x, HasGradientAt f (grad x) x) ∧
      (∀ x y, ‖grad x-grad y‖ ≤ ‖x-y‖) ∧ f 0=0 ∧ (∀ x, 0 ≤ f x) ∧
      ∀ i, grad (z i+g i)=g i ∧ f (z i+g i)=d i+‖g i‖^2/2 := by
  let rows := List.ofFn (fun i => (g i,inner ℝ (g i) (z i)-d i))
  have hr : ∀ r ∈ rows, 0 ≤ r.2 := by
    intro r h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact sub_nonneg.mpr (hc i)
  let P := planeEpigraph rows hr
  refine ⟨envelope P,gradient P,envelope_convex P,envelope_hasGradientAt P,
    gradient_lipschitz P,envelope_zero P,envelope_nonnegative P,fun i => ?_⟩
  apply envelope_interpolates P (z i) (g i) (d i)
  apply active_plane_supports rows hr (z i) (g i) (d i) (hd i)
  · exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · intro r h
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
    have hh := hi j i
    simp only [inner_sub_right] at hh
    dsimp
    linarith

end
end StrongSilver.Moreau
