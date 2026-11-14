-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.ODE.ExistUnique

namespace StrongSilver
open Set Metric
open scoped NNReal
noncomputable section

/-- A globally bounded, uniformly Lipschitz field has a solution on the entire
given compact interval, including a prescribed terminal value. -/
theorem exists_bounded_ode_terminal {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {a b : ℝ} (hab : a ≤ b) (f : ℝ → V → V) (K M : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, LipschitzWith K (f t))
    (hc : ∀ x, ContinuousOn (fun t => f t x) (Icc a b))
    (hbound : ∀ t ∈ Icc a b, ∀ x, ‖f t x‖ ≤ M) (x₀ : V) :
    ∃ u : ℝ → V, u b = x₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u (f t (u t)) (Icc a b) t := by
  let t₀ : Icc a b := ⟨b,hab,le_rfl⟩
  let R : ℝ≥0 := ⟨M*(b-a),mul_nonneg M.coe_nonneg (sub_nonneg.mpr hab)⟩
  have hf : IsPicardLindelof f t₀ x₀ R 0 M K := {
    lipschitzOnWith := fun t ht => (hL t ht).lipschitzOnWith
    continuousOn := fun x hx => hc x
    norm_le := fun t ht x hx => hbound t ht x
    mul_max_le := by
      change (M : ℝ)*max (b-b) (b-a) ≤ M*(b-a)-0
      rw [sub_self,max_eq_right (sub_nonneg.mpr hab),sub_zero]
  }
  exact hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_bounded_ode_initial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {a b : ℝ} (hab : a ≤ b) (f : ℝ → V → V) (K M : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, LipschitzWith K (f t))
    (hc : ∀ x, ContinuousOn (fun t => f t x) (Icc a b))
    (hbound : ∀ t ∈ Icc a b, ∀ x, ‖f t x‖ ≤ M) (x₀ : V) :
    ∃ u : ℝ → V, u a = x₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u (f t (u t)) (Icc a b) t := by
  let t₀ : Icc a b := ⟨a,le_rfl,hab⟩
  let R : ℝ≥0 := ⟨M*(b-a),mul_nonneg M.coe_nonneg (sub_nonneg.mpr hab)⟩
  have hf : IsPicardLindelof f t₀ x₀ R 0 M K := {
    lipschitzOnWith := fun t ht => (hL t ht).lipschitzOnWith
    continuousOn := fun x hx => hc x
    norm_le := fun t ht x hx => hbound t ht x
    mul_max_le := by
      change (M : ℝ)*max (b-a) (a-a) ≤ M*(b-a)-0
      rw [sub_self,max_eq_left (sub_nonneg.mpr hab),sub_zero]
  }
  exact hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

end
end StrongSilver
