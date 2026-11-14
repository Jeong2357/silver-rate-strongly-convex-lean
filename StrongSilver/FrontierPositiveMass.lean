-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedGapObservables
import StrongSilver.BandCutTrees
import StrongSilver.CutRankBudgets

namespace StrongSilver
open ScheduleTree Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3400000

theorem gapObservable_positiveMass (φ : ℝ → ℝ) (κ : ℝ) (finish : ℕ) (C : ScheduleCut) :
    gapObservable (fun _ gap _ => positiveMass (gap.map φ)) κ finish C = positiveMass (C.unselected.map φ) := by
  unfold gapObservable ScheduleCut.unselected ScheduleCut.gaps
  generalize C.phases = ps
  induction ps with
  | nil => simp [positiveMass]
  | cons q ps ih =>
    simp only [List.map_cons,List.sum_cons,List.cons_append,List.flatten_cons,List.map_append,positiveMass_append]
    linear_combination ih

/-- Exact transformed positive mass of all actual frontier gaps. -/
theorem indexedFrontier_positive_mass (φ : ℝ → ℝ) (hφ : Monotone φ) {P κ y : ℝ}
    (hzero : φ 0 ≤ P+Real.exp y) (t : ScheduleTree) (hc : t.Cartesian) :
    ((indexedFrontier φ (P+Real.exp y) 0 κ t).map fun q => positiveMass (q.source.word.map φ)).sum =
      positiveMass ((heightCut φ P y t.word).unselected.map φ) := by
  have hh := indexedFrontier_sum (fun _ gap _ => positiveMass (gap.map φ)) φ hφ (P+Real.exp y) hzero 0 κ t hc
  rw [gapObservable_positiveMass] at hh
  exact hh

theorem fullCut_capped_positive_mass {A B cap μ : ℝ} (hμ : 0 < μ) (hA : 0 < A) (hAB : A ≤ B) (hcap : B ≤ cap)
    (hμB : μ*B ≤ 1/2) (h : List ℝ) :
    positiveMass ((fullCut A h).unselected.map (cappedStep μ B)) ≤
      2*weightedCount h cap*A^(1-nu)/(1-nu) := by
  have hB := hA.trans_le hAB
  have hpoint : ∀ b ∈ (fullCut A h).unselected, max (cappedStep μ B b) 0 ≤ 2*max b 0 := by
    intro b hb
    exact cappedStep_positive_upper hμ hB hμB ((fullCut_unselected hb).trans hAB)
  have hs := List.sum_le_sum hpoint
  simp only [List.sum_map_mul_left] at hs
  have hsum : positiveMass ((fullCut A h).unselected.map (cappedStep μ B)) ≤
      2*positiveMass (fullCut A h).unselected := by
    simpa only [positiveMass,List.map_map,Function.comp_def] using hs
  have hr := (fullCut A h).unselected_positiveMass_rank_bound hA (hAB.trans hcap) (fun b hb _ => fullCut_unselected hb)
  have hword : (fullCut A h).word = h := cutSchedule_word _ _
  rw [hword] at hr
  have hh := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2)
  exact hsum.trans (by linear_combination hh)

end
end StrongSilver
