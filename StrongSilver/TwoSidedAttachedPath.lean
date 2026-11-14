-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TwoSidedSupport
import StrongSilver.AttachedSupportedPath

namespace StrongSilver.SupportedPath
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [ProperSpace (AttachmentSpace V W)]
set_option maxHeartbeats 1600000

theorem exists_two_sided_attached {μ : ℝ} {n m : ℕ} (P : SupportedPath W μ n) (Q : SupportedPath V μ m)
    (hE : P.x (Fin.last n) ≠ 0) (hY : Q.x 0 ≠ 0) {d Ja K C Z H : ℝ}
    (hd : 0 ≤ d) (hdJa : d ≤ Ja) (hfloor : ∀ i, Ja ≤ P.family.d i)
    (hnewg : ∀ i, |inner ℝ (unitDirection (P.x (Fin.last n))) (P.family.g i)| ≤ K)
    (hnewz : ∀ i, |inner ℝ (unitDirection (P.x (Fin.last n))) (P.family.z i)| ≤ C)
    (holdz : ∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ Z)
    (holdg : ∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ H)
    (hcostz : (‖Q.x 0‖/‖P.x (Fin.last n)‖)*K*Z ≤ (‖Q.x 0‖/‖P.x (Fin.last n)‖)^2*d)
    (hcostg : (‖Q.x 0‖/‖P.x (Fin.last n)‖)*C*H ≤ (‖Q.x 0‖/‖P.x (Fin.last n)‖)^2*(Ja-d)) :
    ∃ J : SupportedPath (AttachmentSpace V W) μ (List.ofFn P.steps++List.ofFn Q.steps).length,
      J.x 0 = alignedAttachment (P.x (Fin.last n)) (Q.x 0) (P.x 0) ∧
      J.x (Fin.last _) = retainedMap (W := W) (Q.x (Fin.last m)) ∧
      List.ofFn J.steps = List.ofFn P.steps++List.ofFn Q.steps ∧
      ∀ k, (∃ i, J.family.z k = alignedAttachment (P.x (Fin.last n)) (Q.x 0) (P.family.z i) ∧
        J.family.g k = alignedAttachment (P.x (Fin.last n)) (Q.x 0) (P.family.g i) ∧
        J.family.d k = (‖Q.x 0‖/‖P.x (Fin.last n)‖)^2*(P.family.d i-d)) ∨
        (∃ j, J.family.z k = retainedMap (W := W) (Q.family.z j) ∧
          J.family.g k = retainedMap (W := W) (Q.family.g j) ∧ J.family.d k = Q.family.d j) := by
  let E := P.x (Fin.last n)
  let Y := Q.x 0
  let u := unitDirection E
  let v := unitDirection Y
  let s := ‖Y‖/‖E‖
  have hu : inner ℝ u u = 1 := unitDirection_inner hE
  have hv : inner ℝ v v = 1 := unitDirection_inner hY
  have hs : 0 ≤ s := div_nonneg (norm_nonneg _) (norm_nonneg _)
  let A := alignedAttachment E Y
  let P₀ := P.transport A (s^2) (sq_nonneg s) (alignedAttachment_inner hE hY)
  let P₁ := P₀.shifted (s^2*d) (mul_nonneg (sq_nonneg s) hd)
    (fun i => mul_le_mul_of_nonneg_left (hdJa.trans (hfloor i)) (sq_nonneg s))
  let Q₁ := Q.transport (retainedMap (W := W)) 1 zero_le_one (fun x y => by rw [retained_inner,one_mul])
  have hPQ : ∀ i j, P₁.family.d i+inner ℝ (P₁.family.g i) (Q₁.family.z j-P₁.family.z i) ≤ Q₁.family.d j := by
    intro i j
    have hh := SupportFamily.two_sided_attached_support P.family Q.family hu hv hs hcostz hnewg holdz i j
    change s^2*P.family.d i-s^2*d+inner ℝ (A (P.family.g i))
      (retainedMap (W := W) (Q.family.z j)-A (P.family.z i)) ≤ 1*Q.family.d j
    change s^2*(P.family.d i-d)+inner ℝ (A (P.family.g i))
      (retainedMap (W := W) (Q.family.z j)-A (P.family.z i)) ≤ Q.family.d j at hh
    nlinarith only [hh]
  have hQP : ∀ j i, Q₁.family.d j+inner ℝ (Q₁.family.g j) (P₁.family.z i-Q₁.family.z j) ≤ P₁.family.d i := by
    intro j i
    have hh := SupportFamily.two_sided_retained_support P.family Q.family hs hcostg hfloor hnewz holdg j i
    change 1*Q.family.d j+inner ℝ (retainedMap (W := W) (Q.family.g j))
      (A (P.family.z i)-retainedMap (W := W) (Q.family.z j)) ≤ s^2*P.family.d i-s^2*d
    change Q.family.d j+inner ℝ (retainedMap (W := W) (Q.family.g j))
      (A (P.family.z i)-retainedMap (W := W) (Q.family.z j)) ≤ s^2*(P.family.d i-d) at hh
    nlinarith only [hh]
  have hjoin : P₁.x (Fin.last n) = Q₁.x 0 := alignedAttachment_endpoint hE hY
  let J := P₁.concatenated Q₁ hPQ hQP
  refine ⟨J,rfl,P₁.concatenated_endpoint Q₁ hPQ hQP hjoin,List.ofFn_get _,?_⟩
  intro k
  apply P₁.concatenated_family_inherits Q₁ hPQ hQP hjoin
    (fun z g t => (∃ i, z = A (P.family.z i) ∧ g = A (P.family.g i) ∧ t = s^2*(P.family.d i-d)) ∨
      (∃ j, z = retainedMap (W := W) (Q.family.z j) ∧ g = retainedMap (W := W) (Q.family.g j) ∧ t = Q.family.d j))
  · intro i
    left
    refine ⟨i,rfl,rfl,?_⟩
    change s^2*P.family.d i-s^2*d = s^2*(P.family.d i-d)
    ring
  · intro j; exact Or.inr ⟨j,rfl,rfl,one_mul _⟩

end
end StrongSilver.SupportedPath
