-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteCutCost

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1600000

theorem CutAssembly.mem_reserved {s : CutAssembly} {q : CutPhase} (hq : q ∈ s.reserved) : q ∈ s.phases := by
  induction s <;> simp only [reserved,phases,List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil] at * <;> aesop

theorem CompleteCutAssembly.mem_reserved {s : CompleteCutAssembly} {q : CutPhase} (hq : q ∈ s.reserved) : q ∈ s.phases := by
  cases s with
  | scalar I => exact hq
  | positive s => exact CutAssembly.mem_reserved hq
  | leadingBlock I c s =>
    simp only [reserved,List.mem_append,List.mem_cons] at hq
    simp only [phases,List.mem_append,List.mem_cons]
    rcases hq with hI | rfl | hs
    · exact Or.inl hI
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (CutAssembly.mem_reserved hs))
  | leadingEnd I c => exact hq

theorem transformed_gap_nonnegative_of_cap {A μ : ℝ} (hμ : 0 < μ) (hcap : μ*A ≤ 1/2)
    (h : List ℝ) (hgap : ∀ b ∈ h, 0 < b → b ≤ A) : 0 ≤ transformedGapMaximum μ h := by
  apply transformedGapMaximum_nonnegative hμ h
  intro b hb
  by_cases hb0 : 0 < b
  · have hh := (mul_le_mul_of_nonneg_left (hgap b hb hb0) hμ.le).trans hcap
    linarith only [hh]
  · have hh := mul_nonpos_of_nonneg_of_nonpos hμ.le (le_of_not_gt hb0)
    linarith only [hh]

theorem reference_log_le_growth {A μ P : ℝ} (hμ : 0 < μ) (hcap : μ*A ≤ 1/2) (hP : 1 ≤ P)
    (q : CutPhase) (hb : P < q.pivot) (hgap : ∀ b ∈ q.gap, 0 < b → b ≤ A) :
    Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P)) ≤ phaseGrowthCharge q := by
  have hm := transformed_gap_nonnegative_of_cap hμ hcap q.gap hgap
  have hden : 1 ≤ transformedGapMaximum μ q.gap+P := by linarith only [hm,hP]
  have hden0 := zero_lt_one.trans_le hden
  have hb0 : 0 ≤ q.pivot := zero_le_one.trans (hP.trans hb.le)
  have hnum := sub_pos.mpr hb
  have hr0 := div_pos hnum hden0
  have hpiv : (q.pivot-P)/(transformedGapMaximum μ q.gap+P) ≤ q.pivot := by
    apply (div_le_iff₀ hden0).mpr
    have hh := mul_le_mul_of_nonneg_left hden hb0
    nlinarith only [hh,hP]
  have hh := Real.log_le_log hr0 (hpiv.trans (by linarith only [le_max_left q.pivot 0] : q.pivot ≤ 1+max q.pivot 0))
  have hgaplog := log_one_add_nonnegative (Scalar.SignedIntervals.positiveMass_nonneg q.gap)
  unfold phaseGrowthCharge
  linarith only [hh,hgaplog]

theorem CompleteCutAssembly.reference_restore {A μ P : ℝ} (hμ : 0 < μ) (hcap : μ*A ≤ 1/2) (hP : 1 ≤ P)
    (s : CompleteCutAssembly) (t : List ℝ)
    (hb : ∀ q ∈ s.phases, P < q.pivot) (hgap : ∀ q ∈ s.phases, ∀ b ∈ q.gap, 0 < b → b ≤ A) :
    (s.phases.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum ≤
      s.referenceLog μ P t+(s.reserved.map phaseGrowthCharge).sum := by
  have hh := s.weight_partition (fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P)))
  rw [← s.referenceLog_eq_sum μ P t] at hh
  rw [hh]
  apply add_le_add le_rfl
  apply List.sum_le_sum
  intro q hq
  exact reference_log_le_growth hμ hcap hP q (hb q (mem_reserved hq)) (hgap q (mem_reserved hq))

theorem ScheduleCut.unselected_positiveMass (C : ScheduleCut) :
    Scalar.SignedIntervals.positiveMass C.unselected =
      (C.phases.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum+
        Scalar.SignedIntervals.positiveMass C.terminal := by
  rcases C with ⟨qs,t⟩
  induction qs with
  | nil => simp [unselected,gaps]
  | cons q qs ih =>
    simp only [unselected,gaps,List.map_cons,List.cons_append,List.flatten_cons,
      Scalar.SignedIntervals.positiveMass_append,List.sum_cons] at ih ⊢
    linarith only [ih]

end
end StrongSilver
