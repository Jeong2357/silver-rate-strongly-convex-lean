-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportTransport
import StrongSilver.Trace

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Supporting data are required only before steps, so the endpoint may be
identified with the source of a retained suffix having a different gradient. -/
structure SupportedPath (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (μ : ℝ) (n : ℕ) where
  x : Fin (n+1) → V
  family : SupportFamily (Fin n) V
  steps : Fin n → ℝ
  split : ∀ i, x i.castSucc = family.z i+family.g i
  update : ∀ i : Fin n, x i.succ = x i.castSucc-
    steps i • (μ • x i.castSucc+(1-μ) • family.g i)

namespace SupportedPath
variable {μ : ℝ} {n : ℕ}

theorem follows (P : SupportedPath V μ n) (G : V → V)
    (hG : ∀ i, G (P.x i.castSucc) = μ • P.x i.castSucc+(1-μ) • P.family.g i) :
    iterate (List.ofFn P.steps) G (P.x 0) = P.x (Fin.last n) := by
  apply iterate_of_updates
  intro i
  rw [hG]
  exact P.update i

def transport (P : SupportedPath V μ n) (T : V →ₗ[ℝ] W) (c : ℝ) (hc : 0 ≤ c)
    (hT : ∀ x y, inner ℝ (T x) (T y) = c*inner ℝ x y) : SupportedPath W μ n where
  x := fun i => T (P.x i)
  family := P.family.transport T c hc hT
  steps := P.steps
  split := by intro i; rw [P.split,map_add]; rfl
  update := by
    intro i
    simpa only [map_sub,map_smul,map_add,SupportFamily.transport] using congrArg T (P.update i)

variable [ProperSpace V]

theorem realize (P : SupportedPath V μ n) {κ : ℝ} (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) :
    ∃ f : V → ℝ, ∃ G : V → V, Admissible κ f G ∧ f 0 = 0 ∧ (∀ x, 0 ≤ f x) ∧
      (∀ i, G (P.x i.castSucc) = μ • P.x i.castSucc+(1-μ) • P.family.g i) ∧
      iterate (List.ofFn P.steps) G (P.x 0) = P.x (Fin.last n) := by
  obtain ⟨f,G,hf,h0,hn,hi⟩ := P.family.realize hκ hμ hμ1
  have hG (i) : G (P.x i.castSucc) = μ • P.x i.castSucc+(1-μ) • P.family.g i := by
    simpa only [← P.split] using (hi i).1
  exact ⟨f,G,hf,h0,hn,hG,P.follows G hG⟩

end SupportedPath
end
end StrongSilver
