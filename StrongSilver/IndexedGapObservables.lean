-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedFrontier
import StrongSilver.PositivePartCut
import StrongSilver.HeightCutSelectors

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3200000

/-- Positive-sum excess of one actual signed gap, expressed as a
logarithmic change of its padded mass. -/
def gapLogDeficit (φ : ℝ → ℝ) (P κ : ℝ) (gap : List ℝ) : ℝ :=
  Real.log (gapPrefix (positivePartStep φ) gap+P+κ)-Real.log (gapPrefix φ gap+P+κ)

theorem gapLogDeficit_nonnegative (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (gap : List ℝ) :
    0 ≤ gapLogDeficit φ P κ gap := by
  apply sub_nonneg.mpr
  apply Real.log_le_log
  · have hh := gapPrefix_nonnegative φ gap
    linarith only [hh,hP,hκ]
  · exact add_le_add (add_le_add (gapPrefix_le_positivePart φ gap) le_rfl) le_rfl

theorem gapObservable_savings (φ : ℝ → ℝ) (P κ price : ℝ) (eligible : ℕ → ℝ → Bool) (C : ScheduleCut) :
    gapObservable (fun start gap reserve => gapSavingsMaximum φ P reserve price start gap eligible) κ C.word.length C =
      totalGapSavingsMaximum φ P κ price eligible C := rfl

theorem gapObservable_log_deficit (φ : ℝ → ℝ) (P κ : ℝ) (finish : ℕ) (C : ScheduleCut)
    (hselected : ∀ q ∈ C.phases, 0 ≤ φ q.pivot) :
    gapObservable (fun _ gap reserve => gapLogDeficit φ P reserve gap) κ finish C =
      cutLogProduct (positivePartStep φ) P κ C-cutLogProduct φ P κ C := by
  have hsel : C.phases.map (fun q => Real.log (positivePartStep φ q.pivot-P)) =
      C.phases.map (fun q => Real.log (φ q.pivot-P)) := by
    apply List.map_congr_left
    intro q hq
    rw [positivePartStep,max_eq_left (hselected q hq)]
  have hsum : (C.phases.map fun q => gapLogDeficit φ P 0 q.gap).sum =
      (C.phases.map fun q => Real.log (gapPrefix (positivePartStep φ) q.gap+P)).sum-
        (C.phases.map fun q => Real.log (gapPrefix φ q.gap+P)).sum := by
    generalize C.phases = ps
    induction ps with
    | nil => simp
    | cons q ps ih => simp only [List.map_cons,List.sum_cons,gapLogDeficit,add_zero] at *; linear_combination ih
  unfold gapObservable
  rw [hsum]
  unfold gapLogDeficit cutLogProduct cutMasses
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,
    List.map_map,Function.comp_def,add_zero]
  rw [hsel]
  ring

namespace ScheduleTree

theorem indexedFrontier_savings (φ : ℝ → ℝ) (hφ : Monotone φ) {P κ y : ℝ}
    (hzero : φ 0 ≤ P+Real.exp y) (price : ℝ) (eligible : ℕ → ℝ → Bool) (t : ScheduleTree) (hc : t.Cartesian) :
    ((indexedFrontier φ (P+Real.exp y) 0 κ t).map fun q =>
      gapSavingsMaximum φ P q.reserve price q.start q.source.word eligible).sum =
      totalGapSavingsMaximum φ P κ price eligible (heightCut φ P y t.word) := by
  have hh := indexedFrontier_sum (fun start gap reserve => gapSavingsMaximum φ P reserve price start gap eligible)
    φ hφ (P+Real.exp y) hzero 0 κ t hc
  simp only [Nat.zero_add] at hh
  have hlen := congrArg List.length (cutScheduleFrom_word (fun (_ : ℕ) b => decide (P+Real.exp y < φ b)) 0 t.word)
  rw [← hlen,gapObservable_savings] at hh
  exact hh

theorem indexedFrontier_log_deficit (φ : ℝ → ℝ) (hφ : Monotone φ) {P κ y : ℝ}
    (hP : 0 ≤ P) (hzero : φ 0 ≤ P+Real.exp y) (t : ScheduleTree) (hc : t.Cartesian) :
    ((indexedFrontier φ (P+Real.exp y) 0 κ t).map fun q => gapLogDeficit φ P q.reserve q.source.word).sum =
      cutLogProduct (positivePartStep φ) P κ (heightCut φ P y t.word)-
        cutLogProduct φ P κ (heightCut φ P y t.word) := by
  have hh := indexedFrontier_sum (fun _ gap reserve => gapLogDeficit φ P reserve gap)
    φ hφ (P+Real.exp y) hzero 0 κ t hc
  rw [gapObservable_log_deficit] at hh
  · exact hh
  · intro q hq
    have hsel := cutScheduleFrom_selected_property hq
    have hs : P+Real.exp y < φ q.pivot := of_decide_eq_true hsel
    have he := Real.exp_pos y
    linarith only [hP,hs,he]

end ScheduleTree
end
end StrongSilver
