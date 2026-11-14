-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportProjection
import Mathlib.Analysis.Normed.Module.Convex

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

def bodyOfCompact (S : Set V) (hc : IsCompact S) (h0 : (0 : V) ∈ S) : CompactConvexBody V where
  carrier := closure (convexHull ℝ S)
  compact := Metric.isCompact_of_isClosed_isBounded isClosed_closure
    ((isBounded_convexHull.mpr hc.isBounded).closure)
  convex := (convex_convexHull ℝ S).closure
  zero_mem := subset_closure (subset_convexHull ℝ S h0)

theorem mem_bodyOfCompact {S : Set V} (hc : IsCompact S) (h0 : (0 : V) ∈ S) {v : V} (hv : v ∈ S) :
    v ∈ (bodyOfCompact S hc h0).carrier := subset_closure (subset_convexHull ℝ S hv)

theorem bodyOfCompact_inner_le {S : Set V} (hc : IsCompact S) (h0 : (0 : V) ∈ S) (N : V) (a : ℝ)
    (hS : ∀ v ∈ S, inner ℝ N v ≤ a) : ∀ v ∈ (bodyOfCompact S hc h0).carrier, inner ℝ N v ≤ a := by
  let H : Set V := {v | inner ℝ N v ≤ a}
  have hconv : Convex ℝ H := by
    intro x hx y hy b c hb hc hbc
    change inner ℝ N (b • x+c • y) ≤ a
    simp only [inner_add_right,inner_smul_right,smul_eq_mul]
    change inner ℝ N x ≤ a at hx
    change inner ℝ N y ≤ a at hy
    have hbx := mul_le_mul_of_nonneg_left hx hb
    have hcy := mul_le_mul_of_nonneg_left hy hc
    have he : (b+c)*a = a := by rw [hbc,one_mul]
    nlinarith only [hbx,hcy,he]
  have hclosed : IsClosed H := isClosed_le (innerSL ℝ N).continuous continuous_const
  exact closure_minimal (convexHull_min hS hconv) hclosed

theorem CompactConvexBody.projection_eq_of_normal (K : CompactConvexBody V) (x v : V)
    (hv : v ∈ K.carrier) (hn : ∀ w ∈ K.carrier, inner ℝ (x-v) (w-v) ≤ 0) : K.projection x = v := by
  have hp := K.projection_normal x v hv
  have hvp := hn (K.projection x) (K.projection_mem x)
  have hh : inner ℝ (K.projection x-v) (K.projection x-v) ≤ 0 := by
    simp only [inner_sub_left,inner_sub_right] at hp hvp ⊢
    linarith
  rw [real_inner_self_eq_norm_sq] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (K.projection x-v)]))

end
end StrongSilver
