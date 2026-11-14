-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportedPath
import StrongSilver.SupportAttachment

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
set_option maxHeartbeats 1000000

namespace SupportedPath
variable {μ : ℝ} {n m : ℕ}

def shifted (P : SupportedPath V μ n) (a : ℝ) (ha : 0 ≤ a)
    (hfloor : ∀ i, a ≤ P.family.d i) : SupportedPath V μ n where
  x := P.x
  family := P.family.shifted a ha hfloor
  steps := P.steps
  split := P.split
  update := P.update

variable [ProperSpace V]

/-- Two compatible supported paths are realized by one actual objective. All
retained query values and gradients occur in the conclusion. -/
theorem realize_joint (P : SupportedPath V μ n) (Q : SupportedPath V μ m)
    {κ : ℝ} (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1)
    (hPQ : ∀ i j, P.family.d i+inner ℝ (P.family.g i) (Q.family.z j-P.family.z i) ≤ Q.family.d j)
    (hQP : ∀ j i, Q.family.d j+inner ℝ (Q.family.g j) (P.family.z i-Q.family.z j) ≤ P.family.d i)
    (hjoin : P.x (Fin.last n) = Q.x 0) :
    ∃ f : V → ℝ, ∃ G : V → V, Admissible κ f G ∧ f 0 = 0 ∧ (∀ x, 0 ≤ f x) ∧
      iterate (List.ofFn P.steps++List.ofFn Q.steps) G (P.x 0) = Q.x (Fin.last m) ∧
      (∀ j, G (Q.x j.castSucc) = μ • Q.x j.castSucc+(1-μ) • Q.family.g j) ∧
      (∀ j, f (Q.x j.castSucc) = (μ/2)*‖Q.x j.castSucc‖^2+
        (1-μ)*(Q.family.d j+‖Q.family.g j‖^2/2)) := by
  let F := P.family.sum Q.family hPQ hQP
  obtain ⟨f,G,hf,h0,hn,hi⟩ := F.realize hκ hμ hμ1
  have hP (i : Fin n) : G (P.x i.castSucc) = μ • P.x i.castSucc+(1-μ) • P.family.g i := by
    have hh := (hi (Sum.inl i)).1
    change G (P.family.z i+P.family.g i) = μ • (P.family.z i+P.family.g i)+(1-μ) • P.family.g i at hh
    simpa only [← P.split] using hh
  have hQ (j : Fin m) : G (Q.x j.castSucc) = μ • Q.x j.castSucc+(1-μ) • Q.family.g j := by
    have hh := (hi (Sum.inr j)).1
    change G (Q.family.z j+Q.family.g j) = μ • (Q.family.z j+Q.family.g j)+(1-μ) • Q.family.g j at hh
    simpa only [← Q.split] using hh
  refine ⟨f,G,hf,h0,hn,?_,hQ,fun j => ?_⟩
  · rw [iterate_append,P.follows G hP,hjoin,Q.follows G hQ]
  · have hh := (hi (Sum.inr j)).2
    change f (Q.family.z j+Q.family.g j) = (μ/2)*‖Q.family.z j+Q.family.g j‖^2+
      (1-μ)*(Q.family.d j+‖Q.family.g j‖^2/2) at hh
    simpa only [← Q.split] using hh

end SupportedPath
end
end StrongSilver
