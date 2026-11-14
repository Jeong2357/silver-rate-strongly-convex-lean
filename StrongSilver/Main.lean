-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WeightedCountBound

namespace StrongSilver
noncomputable section

/-- Theorem 1.1: absolute silver-rate lower bounds for both worst-case
relative errors, for every predetermined signed real schedule and every
horizon, on actual smooth strongly convex objectives in finite dimension. -/
theorem silver_rate_lower_bound : MainLowerBound := by
  obtain ⟨a,ha,ha1,hCount⟩ := exists_weighted_count_bound
  exact main_lower_bound_of_weighted_count_bound ha ha1 hCount

/-- The full quantified type of the main theorem, with one pair of
constants chosen before the condition number and arbitrary schedule. -/
theorem silver_rate_lower_bound_explicit :
    ∃ C κ₀ : ℝ, 0 < C ∧ 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ ≤ κ → ∀ h : List ℝ,
      ENNReal.ofReal (Real.exp (-C*(h.length:ℝ)*κ^(-nu))) ≤ D κ h ∧
      ENNReal.ofReal (Real.exp (-C*(h.length:ℝ)*κ^(-nu))) ≤ E κ h :=
  silver_rate_lower_bound

/-- The same theorem with the paper's horizon and vector-of-steps notation. -/
theorem silver_rate_lower_bound_horizon :
    ∃ C κ₀ : ℝ, 0 < C ∧ 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ ≤ κ → ∀ n : ℕ, ∀ h : Fin n → ℝ,
      ENNReal.ofReal (Real.exp (-C*(n:ℝ)*κ^(-nu))) ≤
        min (D κ (List.ofFn h)) (E κ (List.ofFn h)) := by
  obtain ⟨C,κ₀,hC,hκ₀,H⟩ := silver_rate_lower_bound
  refine ⟨C,κ₀,hC,hκ₀,?_⟩
  intro κ hκ n h
  have hh := H κ hκ (List.ofFn h)
  simpa only [List.length_ofFn] using le_min hh.1 hh.2

end
end StrongSilver
