-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic

namespace StrongSilver
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1800000

/-- A single absolute local Lipschitz bound compares two nearby parameter
vectors; the error depends on their difference, not on their separate
errors from the reference point. -/
theorem contDiff_pair_box_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (hf : ContDiffAt ℝ 1 f x₀) : ∃ C > 0, ∃ δ > 0,
    ∀ x y : Fin n → ℝ, (∀ i, |x i-x₀ i| ≤ δ) → (∀ i, |y i-x₀ i| ≤ δ) →
    ∀ ε : ℝ, 0 ≤ ε → (∀ i, |x i-y i| ≤ ε) → |f x-f y| ≤ C*ε := by
  obtain ⟨K,t,ht,hLip⟩ := hf.exists_lipschitzOnWith
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp ht
  have hK : 0 ≤ (K:ℝ) := K.coe_nonneg
  refine ⟨(K:ℝ)+1,by linarith only [hK],d/2,half_pos hd,?_⟩
  intro x y hx hy ε hε hxy
  have hmem (z : Fin n → ℝ) (hz : ∀ i, |z i-x₀ i| ≤ d/2) : z ∈ t := by
    apply hball
    change dist z x₀ < d
    have hh : dist z x₀ ≤ d/2 := (dist_pi_le_iff (half_pos hd).le).mpr
      (fun i => by simpa only [Real.dist_eq] using hz i)
    exact hh.trans_lt (by linarith only [hd])
  have hdist : dist x y ≤ ε := (dist_pi_le_iff hε).mpr (fun i => by simpa only [Real.dist_eq] using hxy i)
  have hh := (hLip.dist_le_mul x (hmem x hx) y (hmem y hy)).trans
    (mul_le_mul_of_nonneg_left hdist hK)
  rw [Real.dist_eq] at hh
  nlinarith only [hh,hε]

end
end StrongSilver
