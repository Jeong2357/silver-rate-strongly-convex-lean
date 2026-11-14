-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PathFamilyRows

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
    {ι : Type*} [Fintype ι] {μ : ℝ} {n : ℕ}
set_option maxHeartbeats 1800000

/-- A path inside a larger finite family is realized by one actual
objective while retaining every contact in the larger family. -/
theorem SupportedPath.realize_within (P : SupportedPath V μ n) (F : SupportFamily ι V)
    (hrows : P.WithinFamily F) {κ : ℝ} (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) :
    ∃ f : V → ℝ, ∃ G : V → V, Admissible κ f G ∧ f 0 = 0 ∧ (∀ x, 0 ≤ f x) ∧
      (∀ i, G (F.z i+F.g i) = μ • (F.z i+F.g i)+(1-μ) • F.g i ∧
        f (F.z i+F.g i) = (μ/2)*‖F.z i+F.g i‖^2+(1-μ)*(F.d i+‖F.g i‖^2/2)) ∧
      iterate (List.ofFn P.steps) G (P.x 0) = P.x (Fin.last n) := by
  obtain ⟨f,G,hf,h0,hn,hi⟩ := F.realize hκ hμ hμ1
  refine ⟨f,G,hf,h0,hn,hi,P.follows G ?_⟩
  intro k
  obtain ⟨i,hz,hg,hd⟩ := hrows k
  have hx : P.x k.castSucc = F.z i+F.g i := by rw [P.split,hz,hg]
  rw [hx,hg]
  exact (hi i).1

end
end StrongSilver
