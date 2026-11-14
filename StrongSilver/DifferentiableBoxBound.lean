-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi

namespace StrongSilver
open Filter
open scoped Topology
noncomputable section

/-- A derivative at one point gives an absolute linear perturbation bound
on a sufficiently small closed coordinate box. -/
theorem differentiable_box_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x₀) : ∃ C > 0, ∃ δ > 0, ∀ ε : ℝ,
    0 ≤ ε → ε ≤ δ → ∀ x : Fin n → ℝ,
    (∀ i, |x i-x₀ i| ≤ ε) → |f x-f x₀| ≤ C*ε := by
  obtain ⟨C,hC,hbound⟩ := hf.isBigO_sub.exists_pos
  obtain ⟨d,hd,hball⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  refine ⟨C,hC,d/2,half_pos hd,fun ε hε hεd x hx => ?_⟩
  have hdist : dist x x₀ ≤ ε := (dist_pi_le_iff hε).mpr
    (fun i => by simpa only [Real.dist_eq] using hx i)
  have hxd : dist x x₀ < d := hdist.trans_lt (hεd.trans_lt (by linarith only [hd]))
  have hh := hball hxd
  change ‖f x-f x₀‖ ≤ C*‖x-x₀‖ at hh
  rw [Real.norm_eq_abs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hdist) hC.le)

end
end StrongSilver
