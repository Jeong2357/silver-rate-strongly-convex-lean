-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Calculus
import Mathlib.Topology.Order.Compact

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

def OutwardNormal (S : Set V) (x q : V) : Prop :=
  ∀ w ∈ S, inner ℝ q (w-x) ≤ 0

def CoerciveOn (S : Set V) (f : V → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ S, R ≤ ‖x‖ → M ≤ f x

theorem minimizer_outward_normal {S : Set V} (hS : Convex ℝ S) {Φ : V → ℝ}
    {G : V → V} (hG : ∀ x, HasGradientAt Φ (G x) x) {x y : V}
    (hx : x ∈ S) (hmin : ∀ w ∈ S, Φ x-inner ℝ y x ≤ Φ w-inner ℝ y w) :
    OutwardNormal S x (y-G x) := by
  let F : V → ℝ := fun z => Φ z-inner ℝ y z
  have hlocal : IsLocalMinOn F S x := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hmin w hw
  have hd := (hG x).hasFDerivAt.sub (innerSL ℝ y).hasFDerivAt
  intro w hw
  have ht := sub_mem_posTangentConeAt_of_segment_subset (hS.segment_subset hx hw)
  have hder := hlocal.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt ht
  simp only [ContinuousLinearMap.sub_apply,InnerProductSpace.toDual_apply_apply,
    innerSL_apply_apply] at hder
  rw [inner_sub_left]
  linarith

theorem gradient_eq_target_of_normal {S : Set V} {x y gx : V} (hy : y ∈ S)
    (hq : OutwardNormal S x (y-gx)) (horth : inner ℝ (y-gx) (gx-x) = 0) : gx = y := by
  have h := hq y hy
  have he : y-x = (y-gx)+(gx-x) := by abel
  rw [he,inner_add_right,real_inner_self_eq_norm_sq,horth,add_zero] at h
  have hz : ‖y-gx‖ = 0 := by nlinarith [norm_nonneg (y-gx)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

/-- Lemma 3.2, with coercivity written in its quantified norm form. -/
theorem exists_predecessor {S : Set V} (hclosed : IsClosed S) (hconvex : Convex ℝ S)
    (Φ : V → ℝ) (G : V → V) (hG : ∀ x, HasGradientAt Φ (G x) x) (y : V) (hy : y ∈ S)
    (hcoercive : CoerciveOn S (fun x => Φ x-inner ℝ y x))
    (horth : ∀ x ∈ S, ∀ q, OutwardNormal S x q → inner ℝ q (G x-x) = 0) :
    ∃ x ∈ S, G x = y := by
  let F : V → ℝ := fun x => Φ x-inner ℝ y x
  obtain ⟨R0,hR0⟩ := hcoercive (F y)
  let R := max R0 (‖y‖+1)
  have hyR : ‖y‖ ≤ R := by dsimp [R]; linarith [le_max_right R0 (‖y‖+1)]
  have hc : IsCompact (S ∩ Metric.closedBall 0 R) :=
    (isCompact_closedBall (0 : V) R).inter_left hclosed
  have hyK : y ∈ S ∩ Metric.closedBall 0 R := by
    exact ⟨hy,by simpa only [Metric.mem_closedBall,dist_zero_right] using hyR⟩
  have hΦ : Continuous Φ := continuous_iff_continuousAt.mpr (fun x => (hG x).continuousAt)
  have hF : Continuous F := hΦ.sub (innerSL ℝ y).continuous
  obtain ⟨x,hx,hmin⟩ := hc.exists_isMinOn ⟨y,hyK⟩ hF.continuousOn
  have hglobal (w : V) (hw : w ∈ S) : F x ≤ F w := by
    by_cases hn : ‖w‖ ≤ R
    · exact hmin ⟨hw,by simpa only [Metric.mem_closedBall,dist_zero_right] using hn⟩
    · exact (hmin hyK).trans (hR0 w hw ((le_max_left _ _).trans (le_of_not_ge hn)))
  have hnormal := minimizer_outward_normal hconvex hG hx.1 hglobal
  exact ⟨x,hx.1,gradient_eq_target_of_normal hy hnormal (horth x hx.1 _ hnormal)⟩

end
end StrongSilver
