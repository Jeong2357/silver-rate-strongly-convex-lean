-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Predecessor

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
set_option maxHeartbeats 1000000

def oppositeSet (S : Set V) : Set V := {x | -x ∈ S}
def negativeConjugate (F : V → V) (x : V) : V := -F (-x)

theorem oppositeSet_closed {S : Set V} (hs : IsClosed S) : IsClosed (oppositeSet S) := hs.preimage continuous_neg

theorem oppositeSet_convex {S : Set V} (hs : Convex ℝ S) : Convex ℝ (oppositeSet S) := by
  intro x hx y hy a b ha hb hab
  have he : -(a • x+b • y) = a • (-x)+b • (-y) := by module
  change -(a • x+b • y) ∈ S
  rw [he]
  exact hs hx hy ha hb hab

theorem oppositeSet_smul {S : Set V} (hs : ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → t • x ∈ S)
    {x : V} (hx : x ∈ oppositeSet S) {t : ℝ} (ht : 0 ≤ t) : t • x ∈ oppositeSet S := by
  change -(t • x) ∈ S
  rw [← smul_neg]
  exact hs (-x) hx t ht

theorem oppositeSet_normal {S : Set V} {x q : V} (hq : OutwardNormal (oppositeSet S) x q) :
    OutwardNormal S (-x) (-q) := by
  intro w hw
  have hh := hq (-w) (show -w ∈ oppositeSet S from by simpa only [oppositeSet,mem_setOf_eq,neg_neg] using hw)
  have he : (-w)-x = -(w-(-x)) := by abel
  rw [he,inner_neg_right] at hh
  rwa [inner_neg_left]

theorem oppositeSet_normal_orthogonal {S : Set V} (G : V → V)
    (horth : ∀ x ∈ S, ∀ q, OutwardNormal S x q → inner ℝ q (negativeConjugate G x) = 0)
    {x q : V} (hx : x ∈ oppositeSet S) (hq : OutwardNormal (oppositeSet S) x q) : inner ℝ q (G x) = 0 := by
  have hh := horth (-x) hx (-q) (oppositeSet_normal hq)
  simpa only [negativeConjugate,neg_neg,inner_neg_left,inner_neg_right] using hh

theorem negativeConjugate_firm (F : V → V)
    (hfirm : ∀ x y, ‖F x-F y‖^2 ≤ inner ℝ (F x-F y) (x-y)) (x y : V) :
    ‖negativeConjugate F x-negativeConjugate F y‖^2 ≤
      inner ℝ (negativeConjugate F x-negativeConjugate F y) (x-y) := by
  have hh := hfirm (-x) (-y)
  have he : -x-(-y) = -(x-y) := by abel
  have hg : negativeConjugate F x-negativeConjugate F y = -(F (-x)-F (-y)) := by unfold negativeConjugate; abel
  rw [he,inner_neg_right] at hh
  rw [hg,norm_neg,inner_neg_left]
  exact hh

end
end StrongSilver
