-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PathConcatenation
import StrongSilver.PathGluing
import StrongSilver.AttachmentNormalization
import StrongSilver.SupportAttachment

namespace StrongSilver.SupportedPath
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [ProperSpace (AttachmentSpace V W)]
set_option maxHeartbeats 1000000

theorem exists_attached {μ : ℝ} {n m : ℕ} (P : SupportedPath W μ n) (Q : SupportedPath V μ m)
    (hE : P.x (Fin.last n) ≠ 0) (hY : Q.x 0 ≠ 0) {a η : ℝ}
    (ha : 0 ≤ a) (hfloor : ∀ i, a ≤ P.family.d i)
    (hslopes : ∀ i, inner ℝ (P.x (Fin.last n)) (P.family.g i) ≤ 0)
    (hpositive : Q.family.PositiveAt (Q.x 0)) (hgate : Q.family.Gate (Q.x 0) η)
    (hproject : ∀ i, inner ℝ (P.x (Fin.last n)) (P.family.z i) ≤ η*‖P.x (Fin.last n)‖^2) :
    ∃ J : SupportedPath (AttachmentSpace V W) μ (List.ofFn P.steps++List.ofFn Q.steps).length,
      J.x 0 = alignedAttachment (P.x (Fin.last n)) (Q.x 0) (P.x 0) ∧
      J.x (Fin.last _) = retainedMap (W := W) (Q.x (Fin.last m)) ∧
      List.ofFn J.steps = List.ofFn P.steps++List.ofFn Q.steps ∧
      ∀ k, (∃ i, J.family.z k = alignedAttachment (P.x (Fin.last n)) (Q.x 0) (P.family.z i) ∧
        J.family.g k = alignedAttachment (P.x (Fin.last n)) (Q.x 0) (P.family.g i) ∧
        J.family.d k = (‖Q.x 0‖/‖P.x (Fin.last n)‖)^2*(P.family.d i-a)) ∨
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
  let P0 := P.transport A (s^2) (sq_nonneg s) (alignedAttachment_inner hE hY)
  let P1 := P0.shifted (s^2*a) (mul_nonneg (sq_nonneg s) ha)
    (fun i => mul_le_mul_of_nonneg_left (hfloor i) (sq_nonneg s))
  let Q1 := Q.transport (retainedMap (W := W)) 1 zero_le_one
    (fun x y => by rw [retained_inner,one_mul])
  have hgate' : Q.family.Gate (‖Y‖ • v) η := by
    change Q.family.Gate (‖Y‖ • unitDirection Y) η
    rwa [norm_smul_unitDirection hY]
  let H := P.family.attach Q.family hu hv hs ha hfloor
    (fun i => unitDirection_inner_nonpositive (hslopes i))
    (fun j => unitDirection_inner_nonnegative (hpositive.1 j))
    (fun j => unitDirection_inner_nonnegative (hpositive.2 j)) hgate'
    (fun i => alignedAttachment_projection_bound hE (hproject i))
  have hPQ : ∀ i j, P1.family.d i+inner ℝ (P1.family.g i) (Q1.family.z j-P1.family.z i) ≤ Q1.family.d j :=
    fun i j => H.supports (Sum.inl i) (Sum.inr j)
  have hQP : ∀ j i, Q1.family.d j+inner ℝ (Q1.family.g j) (P1.family.z i-Q1.family.z j) ≤ P1.family.d i :=
    fun j i => H.supports (Sum.inr j) (Sum.inl i)
  have hjoin : P1.x (Fin.last n) = Q1.x 0 := alignedAttachment_endpoint hE hY
  let J := P1.concatenated Q1 hPQ hQP
  refine ⟨J,rfl,P1.concatenated_endpoint Q1 hPQ hQP hjoin,?_,?_⟩
  · exact List.ofFn_get _
  · intro k
    apply P1.concatenated_family_inherits Q1 hPQ hQP hjoin
      (fun z g d => (∃ i, z = A (P.family.z i) ∧ g = A (P.family.g i) ∧ d = s^2*(P.family.d i-a)) ∨
        (∃ j, z = retainedMap (W := W) (Q.family.z j) ∧ g = retainedMap (W := W) (Q.family.g j) ∧ d = Q.family.d j))
    · intro i
      left
      refine ⟨i,rfl,rfl,?_⟩
      change s^2*P.family.d i-s^2*a = s^2*(P.family.d i-a)
      ring
    · intro j
      right
      exact ⟨j,rfl,rfl,one_mul _⟩

end
end StrongSilver.SupportedPath
