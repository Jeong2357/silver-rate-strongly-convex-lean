-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.RunSupportedPath
import StrongSilver.PathPrefixes
import StrongSilver.FamilyEpigraph

namespace StrongSilver.SupportedPath
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
variable {μ : ℝ} {n m : ℕ}
set_option maxHeartbeats 1000000

section
variable (P : SupportedPath V μ n) (Q : SupportedPath V μ m)
  (hPQ : ∀ i j, P.family.d i+inner ℝ (P.family.g i) (Q.family.z j-P.family.z i) ≤ Q.family.d j)
  (hQP : ∀ j i, Q.family.d j+inner ℝ (Q.family.g j) (P.family.z i-Q.family.z j) ≤ P.family.d i)

def concatenated : SupportedPath V μ (List.ofFn P.steps++List.ofFn Q.steps).length :=
  ofRun (P.family.sum Q.family hPQ hQP).epigraph μ (List.ofFn P.steps++List.ofFn Q.steps) (P.x 0)

theorem joint_gradient_prefix (i : Fin n) :
    stronglyConvexGradient μ (Moreau.gradient (P.family.sum Q.family hPQ hQP).epigraph) (P.x i.castSucc) =
      μ • P.x i.castSucc+(1-μ) • P.family.g i := by
  have hh := ((P.family.sum Q.family hPQ hQP).epigraph_interpolates (Sum.inl i)).1
  change Moreau.gradient _ (P.family.z i+P.family.g i) = P.family.g i at hh
  rw [← P.split] at hh
  unfold stronglyConvexGradient
  rw [hh]

theorem joint_gradient_suffix (j : Fin m) :
    stronglyConvexGradient μ (Moreau.gradient (P.family.sum Q.family hPQ hQP).epigraph) (Q.x j.castSucc) =
      μ • Q.x j.castSucc+(1-μ) • Q.family.g j := by
  have hh := ((P.family.sum Q.family hPQ hQP).epigraph_interpolates (Sum.inr j)).1
  change Moreau.gradient _ (Q.family.z j+Q.family.g j) = Q.family.g j at hh
  rw [← Q.split] at hh
  unfold stronglyConvexGradient
  rw [hh]

theorem joint_query_classification (hjoin : P.x (Fin.last n) = Q.x 0)
    (j : ℕ) (hj : j < (List.ofFn P.steps++List.ofFn Q.steps).length) :
    ∃ i : Fin n ⊕ Fin m,
      iterate ((List.ofFn P.steps++List.ofFn Q.steps).take j)
        (stronglyConvexGradient μ (Moreau.gradient (P.family.sum Q.family hPQ hQP).epigraph)) (P.x 0) =
      (P.family.sum Q.family hPQ hQP).z i+(P.family.sum Q.family hPQ hQP).g i := by
  let G := stronglyConvexGradient μ (Moreau.gradient (P.family.sum Q.family hPQ hQP).epigraph)
  have hP := P.joint_gradient_prefix Q hPQ hQP
  have hQ := P.joint_gradient_suffix Q hPQ hQP
  by_cases hpre : j < n
  · let i : Fin n := ⟨j,hpre⟩
    refine ⟨Sum.inl i,?_⟩
    change iterate ((List.ofFn P.steps++List.ofFn Q.steps).take j) G (P.x 0) = P.family.z i+P.family.g i
    rw [List.take_append_of_le_length (by simp only [List.length_ofFn]; omega)]
    rw [← P.split]
    exact P.follows_prefix G hP i.castSucc
  · have hpost : j-n < m := by simp only [List.length_append,List.length_ofFn] at hj; omega
    let i : Fin m := ⟨j-n,hpost⟩
    refine ⟨Sum.inr i,?_⟩
    change iterate ((List.ofFn P.steps++List.ofFn Q.steps).take j) G (P.x 0) = Q.family.z i+Q.family.g i
    rw [List.take_append,List.take_of_length_le (by simp only [List.length_ofFn]; omega),
      iterate_append,P.follows G hP,hjoin]
    simp only [List.length_ofFn]
    rw [← Q.split]
    exact Q.follows_prefix G hQ i.castSucc

theorem concatenated_family_inherits (hjoin : P.x (Fin.last n) = Q.x 0)
    (R : V → V → ℝ → Prop) (hP : ∀ i, R (P.family.z i) (P.family.g i) (P.family.d i))
    (hQ : ∀ j, R (Q.family.z j) (Q.family.g j) (Q.family.d j))
    (k : Fin (List.ofFn P.steps++List.ofFn Q.steps).length) :
    R ((P.concatenated Q hPQ hQP).family.z k) ((P.concatenated Q hPQ hQP).family.g k)
      ((P.concatenated Q hPQ hQP).family.d k) := by
  let F := P.family.sum Q.family hPQ hQP
  obtain ⟨i,hi⟩ := P.joint_query_classification Q hPQ hQP hjoin k.val k.isLt
  have he := (F.epigraph_interpolates i).2
  have hg := (F.epigraph_interpolates i).1
  have hz : Moreau.proximal F.epigraph (F.z i+F.g i) = F.z i := by
    unfold Moreau.proximal
    rw [he]
  change R (Moreau.proximal F.epigraph (iterate _ _ _)) (Moreau.gradient F.epigraph (iterate _ _ _))
    (Moreau.minimizingPair F.epigraph (iterate _ _ _)).2
  simp only [Fin.val_castSucc]
  rw [hi,hz,hg,he]
  cases i with | inl i => exact hP i | inr j => exact hQ j

theorem concatenated_endpoint (hjoin : P.x (Fin.last n) = Q.x 0) :
    (P.concatenated Q hPQ hQP).x (Fin.last (List.ofFn P.steps++List.ofFn Q.steps).length) = Q.x (Fin.last m) := by
  rw [concatenated,ofRun_end,iterate_append,P.follows _ (P.joint_gradient_prefix Q hPQ hQP),hjoin,
    Q.follows _ (P.joint_gradient_suffix Q hPQ hQP)]

end
end
end StrongSilver.SupportedPath
