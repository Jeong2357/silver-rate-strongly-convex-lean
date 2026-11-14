-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Predecessor
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.Filter.Finite

namespace StrongSilver
open Set Filter
open scoped Topology
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}

def linearCone (L : ι → V →L[ℝ] ℝ) : Set V := {x | ∀ i, 0 ≤ L i x}

theorem linearCone_closed (L : ι → V →L[ℝ] ℝ) : IsClosed (linearCone L) := by
  have he : linearCone L = ⋂ i, {x | (0 : ℝ) ≤ L i x} := by ext x; simp only [linearCone,mem_setOf_eq,mem_iInter]
  rw [he]
  exact isClosed_iInter (fun i => isClosed_le continuous_const (L i).continuous)

theorem linearCone_convex (L : ι → V →L[ℝ] ℝ) : Convex ℝ (linearCone L) := by
  intro x hx y hy a b ha hb hab i
  simp only [map_add,map_smul,smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem linearCone_smul (L : ι → V →L[ℝ] ℝ) {x : V} (hx : x ∈ linearCone L)
    {t : ℝ} (ht : 0 ≤ t) : t • x ∈ linearCone L := by
  intro i
  rw [map_smul,smul_eq_mul]
  exact mul_nonneg ht (hx i)

variable [Fintype ι]
set_option maxHeartbeats 1000000

/-- A vector tangent to every active face is orthogonal to all outward normals.
This avoids assuming a classification of normal cones. -/
theorem linearCone_normal_orthogonal (L : ι → V →L[ℝ] ℝ) {x v q : V}
    (hx : x ∈ linearCone L) (hv : ∀ i, L i x = 0 → L i v = 0)
    (hq : OutwardNormal (linearCone L) x q) : inner ℝ q v = 0 := by
  have he (i : ι) : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ L i (x+t • v) := by
    by_cases hi : L i x = 0
    · apply Eventually.of_forall
      intro t
      rw [map_add,map_smul,hi,hv i hi,smul_eq_mul,mul_zero,add_zero]
    · have hp : 0 < L i x := lt_of_le_of_ne (hx i) (Ne.symm hi)
      have hc : Continuous (fun t : ℝ => L i (x+t • v)) := by fun_prop
      have hp0 : 0 < L i (x+(0 : ℝ) • v) := by simpa only [zero_smul,add_zero] using hp
      exact ((tendsto_order.1 hc.continuousAt).1 0 hp0).mono (fun t ht => ht.le)
  have hall : ∀ᶠ t : ℝ in 𝓝 0, x+t • v ∈ linearCone L := Filter.eventually_all.mpr he
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hall
  let t : ℝ := ε/2
  have ht : 0 < t := div_pos hε (by norm_num)
  have hplus : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
    dsimp [t]
    linarith
  have hminus : -t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_neg (neg_neg_of_pos ht),neg_neg]
    dsimp [t]
    linarith
  have hp := hq (x+t • v) (hball hplus)
  have hm := hq (x+(-t) • v) (hball hminus)
  have hep : x+t • v-x = t • v := by abel
  have hem : x+(-t) • v-x = (-t) • v := by abel
  rw [hep,real_inner_smul_right] at hp
  rw [hem,real_inner_smul_right] at hm
  nlinarith only [hp,hm,ht]

end
end StrongSilver
