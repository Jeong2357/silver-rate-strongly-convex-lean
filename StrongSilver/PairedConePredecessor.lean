-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeBackwardStep
import StrongSilver.OppositeDomain

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
set_option maxHeartbeats 1000000

theorem paired_cone_predecessor {μ b K : ℝ} (hμ : 0 < μ) {S : Set V}
    (hclosed : IsClosed S) (hconvex : Convex ℝ S)
    (hcone : ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → t • x ∈ S)
    (F : V → ℝ) (G : V → V) (hG : ∀ x, HasGradientAt F (G x) x)
    (hlower : ∀ x, (μ/2)*‖x‖^2 ≤ F x) (hupper : ∀ x, F x ≤ (μ/2)*‖x‖^2+K*‖x‖)
    (horth : ∀ x ∈ S, ∀ q, OutwardNormal S x q → inner ℝ q (G x) = 0)
    (hopp : ∀ x ∈ oppositeSet S, ∀ q, OutwardNormal (oppositeSet S) x q → inner ℝ q (G x) = 0)
    (hb : 1-μ*b ≠ 0) {y : V} (hy : y ∈ S ∪ oppositeSet S) :
    ∃ x ∈ S ∪ oppositeSet S, x-b • G x = y := by
  have hoc := oppositeSet_closed hclosed
  have hov := oppositeSet_convex hconvex
  have hos : ∀ x ∈ oppositeSet S, ∀ t : ℝ, 0 ≤ t → t • x ∈ oppositeSet S :=
    fun x hx t ht => oppositeSet_smul hcone hx ht
  by_cases hpos : 0 < 1-μ*b
  · rcases hy with hy | hy
    · obtain ⟨x,hx,he⟩ := exists_backward_step_in_domain hclosed hconvex F G hG hlower hupper hpos horth y hy
      exact ⟨x,Or.inl hx,he⟩
    · obtain ⟨x,hx,he⟩ := exists_backward_step_in_domain hoc hov F G hG hlower hupper hpos hopp y hy
      exact ⟨x,Or.inr hx,he⟩
  · have hlarge : 1 < μ*b := by rcases lt_or_gt_of_ne hb with hh | hh <;> linarith
    have hbpos : 0 < b := by
      by_contra hn
      have hm := mul_nonpos_of_nonneg_of_nonpos hμ.le (le_of_not_gt hn)
      linarith only [hlarge,hm]
    rcases hy with hy | hy
    · have hmy : -y ∈ oppositeSet S := by simpa only [oppositeSet,mem_setOf_eq,neg_neg] using hy
      obtain ⟨x,hx,he⟩ := exists_backward_step_negative_coefficient hoc hov hos F G hG hlower hbpos.le hlarge hopp y hmy
      exact ⟨x,Or.inr hx,he⟩
    · obtain ⟨x,hx,he⟩ := exists_backward_step_negative_coefficient hclosed hconvex hcone F G hG hlower hbpos.le hlarge horth y hy
      exact ⟨x,Or.inl hx,he⟩

end
end StrongSilver
