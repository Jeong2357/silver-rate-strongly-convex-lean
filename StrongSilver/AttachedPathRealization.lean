-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PathGluing
import StrongSilver.AttachmentNormalization

namespace StrongSilver.SupportedPath
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [ProperSpace (AttachmentSpace V W)]
set_option maxHeartbeats 1000000

/-- A local path is aligned with an arbitrary retained suffix and realized by
one admissible objective, preserving the suffix's exact values and slopes. -/
theorem attach_actual {μ κ : ℝ} {n m : ℕ} (P : SupportedPath W μ n) (Q : SupportedPath V μ m)
    (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1)
    (hE : P.x (Fin.last n) ≠ 0) (hY : Q.x 0 ≠ 0) {a η : ℝ}
    (ha : 0 ≤ a) (hfloor : ∀ i, a ≤ P.family.d i)
    (hslopes : ∀ i, inner ℝ (P.x (Fin.last n)) (P.family.g i) ≤ 0)
    (hpositive : Q.family.PositiveAt (Q.x 0)) (hgate : Q.family.Gate (Q.x 0) η)
    (hproject : ∀ i, inner ℝ (P.x (Fin.last n)) (P.family.z i) ≤ η*‖P.x (Fin.last n)‖^2) :
    ∃ f : AttachmentSpace V W → ℝ, ∃ G : AttachmentSpace V W → AttachmentSpace V W,
      Admissible κ f G ∧ f 0 = 0 ∧ (∀ x, 0 ≤ f x) ∧
      iterate (List.ofFn P.steps++List.ofFn Q.steps) G
        (alignedAttachment (P.x (Fin.last n)) (Q.x 0) (P.x 0)) = retainedMap (W := W) (Q.x (Fin.last m)) ∧
      (∀ j, G (retainedMap (W := W) (Q.x j.castSucc)) =
        μ • retainedMap (W := W) (Q.x j.castSucc)+(1-μ) • retainedMap (W := W) (Q.family.g j)) ∧
      (∀ j, f (retainedMap (W := W) (Q.x j.castSucc)) =
        (μ/2)*‖Q.x j.castSucc‖^2+(1-μ)*(Q.family.d j+‖Q.family.g j‖^2/2)) := by
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
  have hnew : ∀ i, inner ℝ u (P.family.g i) ≤ 0 := fun i => unitDirection_inner_nonpositive (hslopes i)
  have hz : ∀ j, 0 ≤ inner ℝ v (Q.family.z j) := fun j => unitDirection_inner_nonnegative (hpositive.1 j)
  have hg : ∀ j, 0 ≤ inner ℝ v (Q.family.g j) := fun j => unitDirection_inner_nonnegative (hpositive.2 j)
  have hgate' : Q.family.Gate (‖Y‖ • v) η := by
    change Q.family.Gate (‖Y‖ • unitDirection Y) η
    rwa [norm_smul_unitDirection hY]
  have hp : ∀ i, s*inner ℝ u (P.family.z i) ≤ η*‖Y‖ :=
    fun i => alignedAttachment_projection_bound hE (hproject i)
  have hPQ : ∀ i j, P1.family.d i+inner ℝ (P1.family.g i) (Q1.family.z j-P1.family.z i) ≤ Q1.family.d j := by
    intro i j
    have hh := SupportFamily.attached_support_at_retained P.family Q.family hu hv hs ha hnew hz i j
    change s^2*P.family.d i-s^2*a+inner ℝ (attachmentMap u v s (P.family.g i))
      (retainedMap (W := W) (Q.family.z j)-attachmentMap u v s (P.family.z i)) ≤ 1*Q.family.d j
    simpa only [one_mul] using hh.trans (Q.family.nonnegative j)
  have hQP : ∀ j i, Q1.family.d j+inner ℝ (Q1.family.g j) (P1.family.z i-Q1.family.z j) ≤ P1.family.d i := by
    intro j i
    have hh := SupportFamily.retained_support_at_attached P.family Q.family u v s ‖Y‖ η hg hgate' hp i j
    change 1*Q.family.d j+inner ℝ (retainedMap (W := W) (Q.family.g j))
      (attachmentMap u v s (P.family.z i)-retainedMap (W := W) (Q.family.z j)) ≤ s^2*P.family.d i-s^2*a
    rw [one_mul]
    exact hh.trans (sub_nonneg.mpr (mul_le_mul_of_nonneg_left (hfloor i) (sq_nonneg s)))
  have hjoin : P1.x (Fin.last n) = Q1.x 0 := alignedAttachment_endpoint hE hY
  obtain ⟨f,G,hf,h0,hn,hrun,hgrad,hvalue⟩ := P1.realize_joint Q1 hκ hμ hμ1 hPQ hQP hjoin
  refine ⟨f,G,hf,h0,hn,hrun,hgrad,fun j => ?_⟩
  have hq := hvalue j
  change f (retainedMap (W := W) (Q.x j.castSucc)) =
    (μ/2)*‖retainedIsometry (W := W) (Q.x j.castSucc)‖^2+
      (1-μ)*(1*Q.family.d j+‖retainedIsometry (W := W) (Q.family.g j)‖^2/2) at hq
  simpa only [LinearIsometry.norm_map,one_mul] using hq

end
end StrongSilver.SupportedPath
