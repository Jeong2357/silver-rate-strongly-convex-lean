-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.StrongMoreau

namespace StrongSilver
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

theorem finite_strong_interpolation {κ μ : ℝ} (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) (n : ℕ)
    (z g : Fin n → V) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (ho : ∀ i, d i ≤ inner ℝ (g i) (z i))
    (hs : ∀ i j, d i + inner ℝ (g i) (z j-z i) ≤ d j) :
    ∃ f : V → ℝ, ∃ G : V → V, Admissible κ f G ∧ f 0 = 0 ∧ (∀ x, 0 ≤ f x) ∧
      ∀ i, G (z i+g i) = μ • (z i+g i)+(1-μ) • g i ∧
        f (z i+g i) = (μ/2)*‖z i+g i‖^2+(1-μ)*(d i+‖g i‖^2/2) := by
  obtain ⟨f,G,hf,hG,hL,hzero,hnonneg,hi⟩ :=
    Moreau.finite_smooth_interpolation n z g d hd ho hs
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hμ0 : 0 ≤ μ := le_trans (by positivity) hμ
  refine ⟨stronglyConvexObjective μ f,stronglyConvexGradient μ G,
    strongify_admissible_curvature hκ hμ hμ1 hf hG hL,?_,?_,?_⟩
  · simp [stronglyConvexObjective,hzero]
  · intro x
    exact add_nonneg (mul_nonneg (div_nonneg hμ0 (by norm_num)) (sq_nonneg _))
      (mul_nonneg (sub_nonneg.mpr hμ1) (hnonneg x))
  · intro i
    obtain ⟨hg,hvalue⟩ := hi i
    simp only [stronglyConvexGradient,stronglyConvexObjective,hg,hvalue,and_self]

end
end StrongSilver
