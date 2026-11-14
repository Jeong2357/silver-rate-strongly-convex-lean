-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteInterpolation
import Mathlib.Topology.MetricSpace.Lipschitz

namespace StrongSilver
open Set
open scoped NNReal
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

structure CompactConvexBody (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  carrier : Set V
  compact : IsCompact carrier
  convex : Convex ℝ carrier
  zero_mem : (0 : V) ∈ carrier

namespace CompactConvexBody

theorem exists_support_point (K : CompactConvexBody V) (u : V) :
    ∃ v ∈ K.carrier, ∀ w ∈ K.carrier, inner ℝ u w ≤ inner ℝ u v :=
  K.compact.exists_isMaxOn ⟨0,K.zero_mem⟩ (innerSL ℝ u).continuous.continuousOn

def supportPoint (K : CompactConvexBody V) (u : V) : V := (K.exists_support_point u).choose
def supportValue (K : CompactConvexBody V) (u : V) : ℝ := inner ℝ u (K.supportPoint u)

theorem supportPoint_mem (K : CompactConvexBody V) (u : V) : K.supportPoint u ∈ K.carrier :=
  (K.exists_support_point u).choose_spec.1

theorem inner_le_supportValue (K : CompactConvexBody V) (u w : V) (hw : w ∈ K.carrier) :
    inner ℝ u w ≤ K.supportValue u := (K.exists_support_point u).choose_spec.2 w hw

theorem supportValue_le (K : CompactConvexBody V) (u : V) (a : ℝ) :
    K.supportValue u ≤ a ↔ ∀ w ∈ K.carrier, inner ℝ u w ≤ a := by
  constructor
  · intro ha w hw
    exact (K.inner_le_supportValue u w hw).trans ha
  · intro ha
    exact ha _ (K.supportPoint_mem u)

theorem supportValue_nonnegative (K : CompactConvexBody V) (u : V) : 0 ≤ K.supportValue u := by
  simpa only [inner_zero_right] using K.inner_le_supportValue u 0 K.zero_mem

theorem supportValue_zero (K : CompactConvexBody V) : K.supportValue 0 = 0 := by
  simp only [supportValue,inner_zero_left]

theorem exists_norm_bound (K : CompactConvexBody V) : ∃ M : ℝ≥0, ∀ v ∈ K.carrier, ‖v‖ ≤ M := by
  obtain ⟨M,hM⟩ := K.compact.exists_bound_of_continuousOn continuous_id.continuousOn
  refine ⟨⟨max M 0,le_max_right _ _⟩,fun v hv => (hM v hv).trans (le_max_left _ _)⟩

theorem supportValue_increment (K : CompactConvexBody V) {M : ℝ≥0}
    (hM : ∀ v ∈ K.carrier, ‖v‖ ≤ M) (x y : V) :
    K.supportValue x ≤ K.supportValue y+M*‖x-y‖ := by
  have hs := K.inner_le_supportValue y (K.supportPoint x) (K.supportPoint_mem x)
  have hi := real_inner_le_norm (x-y) (K.supportPoint x)
  rw [inner_sub_left] at hi
  have hb := mul_le_mul_of_nonneg_left (hM _ (K.supportPoint_mem x)) (norm_nonneg (x-y))
  unfold supportValue at *
  nlinarith only [hs,hi,hb]

theorem supportValue_continuous (K : CompactConvexBody V) : Continuous K.supportValue := by
  obtain ⟨M,hM⟩ := K.exists_norm_bound
  apply (LipschitzWith.of_le_add_mul M (fun x y => ?_)).continuous
  simpa only [dist_eq_norm] using K.supportValue_increment hM x y

theorem supportValue_convex (K : CompactConvexBody V) : ConvexOn ℝ univ K.supportValue := by
  refine ⟨convex_univ,fun x hx y hy a b ha hb hab => ?_⟩
  change K.supportValue (a • x+b • y) ≤ a*K.supportValue x+b*K.supportValue y
  apply (K.supportValue_le _ _).mpr
  intro w hw
  have hxw := mul_le_mul_of_nonneg_left (K.inner_le_supportValue x w hw) ha
  have hyw := mul_le_mul_of_nonneg_left (K.inner_le_supportValue y w hw) hb
  simp only [inner_add_left,real_inner_smul_left]
  linarith

def supportEpigraph (K : CompactConvexBody V) : Moreau.Epigraph V :=
  Moreau.finiteEpigraph K.supportValue K.supportValue_continuous K.supportValue_convex
    K.supportValue_nonnegative K.supportValue_zero

end CompactConvexBody
end
end StrongSilver
