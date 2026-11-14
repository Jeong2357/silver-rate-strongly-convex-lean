-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusBoundary

namespace StrongSilver.Scalar.Silver
open Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem splitPotential_comm (a b : ℝ) : splitPotential a b=splitPotential b a := by
  unfold splitPotential
  rw [add_comm a b,add_comm (scalarPotential a) (scalarPotential b)]

/-- A uniform positive barrier outside a genuine compact rectangle in the
positive quadrant. This proves the boundary assertion used in the paper. -/
theorem splitPotential_compact_barrier : ∃ l U : ℝ, 0 < l ∧ l < U ∧
    ∀ a b : ℝ, 0 < a → 0 < b → (a ∉ Icc l U ∨ b ∉ Icc l U) →
      minimum/2 ≤ splitPotential a b := by
  obtain ⟨A₀,hA₀⟩ := eventually_atTop.mp (largeBarrier_tendsto.eventually_ge_atTop (minimum/2))
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  have hlarge (a : ℝ) (ha : A ≤ a) : minimum/2 ≤ largeBarrier a :=
    hA₀ a ((le_max_right _ _).trans ha)
  have htail : Tendsto (fun b : ℝ => (A+1)*tailSlopeBound b) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul tailSlopeBound_tendsto :
      Tendsto (fun b : ℝ => (A+1)*tailSlopeBound b) atTop (𝓝 ((A+1)*0)))
  have htailSmall : ∀ᶠ b : ℝ in atTop, (A+1)*tailSlopeBound b < minimum/2 :=
    (tendsto_order.mp htail).2 _ (by linarith [minimum_positive])
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp htailSmall
  let B := max (A+1) B₀
  have hBA : A+1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := by linarith
  have htailBound (b : ℝ) (hb : B ≤ b) : (A+1)*tailSlopeBound b < minimum/2 :=
    hB₀ b ((le_max_right _ _).trans hb)
  have hcont : ContinuousOn scalarPotential (Icc 1 (2*B+1)) := by
    intro x hx
    exact (scalarPotential_derivative x (by linarith [hx.1])).continuousAt.continuousWithinAt
  obtain ⟨z,hz,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1 : ℝ) (2*B+1)).Nonempty from ⟨1,le_rfl,by linarith⟩) hcont
  let M := scalarPotential z
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, M+minimum ≤ scalarPotential a :=
    scalarPotential_tendsto_zero.eventually_ge_atTop _
  obtain ⟨r,hr,hrsmall⟩ := Metric.mem_nhdsWithin_iff.mp hsmall
  let l := min (r/2) 1
  have hl : 0 < l := lt_min (by linarith) zero_lt_one
  have hlr : l < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hlB : l < B := by have h := min_le_right (r/2) (1 : ℝ); linarith
  have hsmallBound (a : ℝ) (ha : 0 < a) (hal : a < l) : M+minimum ≤ scalarPotential a := by
    apply hrsmall
    refine ⟨?_,ha⟩
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ha]
    exact hal.trans hlr
  have hordered (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
      (hout : a ∉ Icc l B ∨ b ∉ Icc l B) : minimum/2 ≤ splitPotential a b := by
    by_cases haA : A ≤ a
    · exact (hlarge a haA).trans (splitPotential_large_lower a b ha hab)
    · have haAle : a ≤ A := (lt_of_not_ge haA).le
      by_cases hbB : B ≤ b
      · have hbound := bounded_small_large A a b ha haAle hb
        have htail := htailBound b hbB
        linarith
      · have hbBl : b < B := lt_of_not_ge hbB
        have hal : a < l := by
          by_contra hn
          have hla : l ≤ a := le_of_not_gt hn
          have hma : a ∈ Icc l B := ⟨hla,hab.trans hbBl.le⟩
          have hmb : b ∈ Icc l B := ⟨hla.trans hab,hbBl.le⟩
          exact hout.elim (fun h => h hma) (fun h => h hmb)
        have hfa := hsmallBound a ha hal
        have hfb := scalarPotential_lower b hb
        have hZ : a+b+1 ∈ Icc 1 (2*B+1) := ⟨by linarith,by linarith⟩
        have hZmax : scalarPotential (a+b+1) ≤ M := hmax hZ
        unfold splitPotential
        linarith [minimum_positive]
  refine ⟨l,B,hl,hlB,fun a b ha hb hout => ?_⟩
  rcases le_total a b with hab | hba
  · exact hordered a b ha hb hab hout
  · rw [splitPotential_comm]
    exact hordered b a hb ha hba hout.symm

end
end StrongSilver.Scalar.Silver
