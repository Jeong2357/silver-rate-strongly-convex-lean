-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PhaseMarkingBudget
import StrongSilver.LayerCake

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

theorem ScheduleCut.unselected_positiveMass_le_clipped {A : ℝ} (hA : 0 ≤ A) (C : ScheduleCut)
    (hcap : ∀ b ∈ C.unselected, 0 < b → b ≤ A) :
    Scalar.SignedIntervals.positiveMass C.unselected ≤ clippedMass C.word A := by
  have he : Scalar.SignedIntervals.positiveMass C.unselected = clippedMass C.unselected A := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    have hbA : b ≤ A := by
      by_cases hp : 0 < b
      · exact hcap b hb hp
      · exact (le_of_not_gt hp).trans hA
    simp only [min_eq_left hbA,max_comm]
  have hh := C.word_sum (fun b => max 0 (min b A))
  have hp : 0 ≤ (C.phases.map fun q => max 0 (min q.pivot A)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
    exact le_max_left _ _
  change clippedMass C.word A = clippedMass C.unselected A+_ at hh
  linarith only [he,hh,hp]

theorem ScheduleCut.unselected_positiveMass_rank_bound {A cap : ℝ} (hA : 0 < A) (hAcap : A ≤ cap)
    (C : ScheduleCut) (hgap : ∀ b ∈ C.unselected, 0 < b → b ≤ A) :
    Scalar.SignedIntervals.positiveMass C.unselected ≤ weightedCount C.word cap*A^(1-nu)/(1-nu) :=
  (C.unselected_positiveMass_le_clipped hA.le hgap).trans (clippedMass_rank_bound C.word hA hAcap)

theorem negativeLogSum_le_logGains {T : ℝ} (hT : 0 < T) (h : List ℝ) :
    negativeLogSum h T ≤ logGains h T := by
  rw [logGains_eq hT]
  have hh : 0 ≤ largeLogSum h T := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    split_ifs with hb
    · exact Real.log_nonneg ((one_le_div hT).mpr hb)
    · exact le_rfl
  linarith only [hh]

theorem stable_negative_log_rank_bound : ∃ C > 0, ∀ κ T cap : ℝ,
    1 < κ → 4 ≤ T → T ≤ κ → T ≤ cap → ∀ h : List ℝ, D κ h ≤ 1 →
      negativeLogSum h T ≤ C*weightedCount h cap*T^(-nu) := by
  obtain ⟨C,hC,hb⟩ := stable_logGains_bound
  exact ⟨C,hC,fun κ T cap hκ hT hTκ hcap h hD =>
    (negativeLogSum_le_logGains (lt_of_lt_of_le (by norm_num) hT) h).trans (hb κ T cap hκ hT hTκ hcap h hD)⟩

/-- Rank control of all three numerical marked-phase tests. -/
theorem stable_cut_three_test_rank_bound : ∃ C > 0, ∀ κ A L M T F cap : ℝ,
    1 < κ → 0 < A → A ≤ cap → 0 < L → L ≤ cap → 0 < M → 4 ≤ T → T ≤ κ → T ≤ cap → 0 < F →
      ∀ S : ScheduleCut, (∀ b ∈ S.unselected, 0 < b → b ≤ A) → D κ S.word ≤ 1 →
      (badPhaseCount (fun q : CutPhase => decide (q.pivot ≤ L ∧ Scalar.SignedIntervals.positiveMass q.gap ≤ M ∧
        negativeLogSum q.gap T ≤ F)) S.phases : ℝ) ≤
        weightedCount S.word cap*L^(-nu)+(weightedCount S.word cap*A^(1-nu)/(1-nu))/M+
          C*weightedCount S.word cap*T^(-nu)/F := by
  obtain ⟨C,hC,hneg⟩ := stable_negative_log_rank_bound
  refine ⟨C,hC,?_⟩
  intro κ A L M T F cap hκ hA hAcap hL hLcap hM hT hTκ hTcap hF S hgap hD
  have hh := cut_three_test_marked_count (L := L) hM (lt_of_lt_of_le (by norm_num) hT) hF S
  have hp := countAbove_rank_bound S.word hL hLcap
  have hm := div_le_div_of_nonneg_right (S.unselected_positiveMass_rank_bound hA hAcap hgap) hM.le
  have hn := div_le_div_of_nonneg_right (hneg κ T cap hκ hT hTκ hTcap S.word hD) hF.le
  linarith only [hh,hp,hm,hn]

end
end StrongSilver
