-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialCutBound
import StrongSilver.WorkingMarkedCount
import StrongSilver.InitialBandParameters

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1800000

def initialPhaseTests (κ : ℝ) (q : CutPhase) : Bool :=
  decide (q.pivot ≤ κ/2 ∧ Scalar.SignedIntervals.positiveMass q.gap ≤ κ ∧ negativeLogSum q.gap κ ≤ 1)

def initialMarkedGood (κ B μ : ℝ) (q : CutPhase) : Bool :=
  initialPhaseTests κ q && initialPhaseGood κ B μ (3*κ/4) q

theorem initialMarkedGood_budget {κ B μ : ℝ} {q : CutPhase} (hq : initialMarkedGood κ B μ q = true) :
    InitialPhaseBudget B μ q.pivot (3*κ/4) κ B q.gap := by
  classical
  have hh : initialPhaseTests κ q = true ∧ initialPhaseGood κ B μ (3*κ/4) q = true := by
    simpa only [initialMarkedGood,Bool.and_eq_true] using hq
  exact of_decide_eq_true hh.2

theorem initial_marked_count_le {κ B μ : ℝ} (hκ : 1 ≤ κ) (hB : 0 < B) (hBκ : B ≤ κ/4)
    (hμ : 1/κ ≤ μ) (hμu : μ ≤ 9/(8*κ)) (qs : List CutPhase)
    (hpiv : ∀ q ∈ qs, B ≤ q.pivot) (hgap : ∀ q ∈ qs, ∀ b ∈ q.gap, 0 < b → b ≤ B) :
    badPhaseCount (initialMarkedGood κ B μ) qs ≤ badPhaseCount (initialPhaseTests κ) qs := by
  classical
  apply badPhaseCount_mono
  intro q hq htest
  obtain ⟨hb,hm,hE⟩ : q.pivot ≤ κ/2 ∧ Scalar.SignedIntervals.positiveMass q.gap ≤ κ ∧ negativeLogSum q.gap κ ≤ 1 :=
    of_decide_eq_true htest
  have hW := initial_budget_of_kappa_band hκ hB hBκ hμ hμu (hpiv q hq) hb q.gap hm hE (hgap q hq)
  simp only [initialMarkedGood,htest,Bool.true_and,initialPhaseGood,decide_eq_true_eq]
  exact hW

theorem list_filter_length_weight {α : Type*} (p : α → Bool) (xs : List α) :
    ((xs.filter p).length : ℝ) = (xs.map fun a => if p a then (1 : ℝ) else 0).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp,ih,add_comm]

theorem list_weight_zero {α : Type*} (w : α → ℝ) (xs : List α) (hw : ∀ a ∈ xs, w a = 0) : (xs.map w).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := hw a (by simp)
    have ht := ih (fun z hz => hw z (List.mem_cons_of_mem a hz))
    simp only [List.map_cons,List.sum_cons,ha,ht,add_zero]

theorem strictLarge_pivots_le_initial_marked (κ : ℝ) (qs : List CutPhase) :
    (qs.filter fun q => decide (κ/2 < q.pivot)).length ≤ badPhaseCount (initialPhaseTests κ) qs := by
  have hh := badPhaseCount_mono (fun q : CutPhase => decide (q.pivot ≤ κ/2)) (initialPhaseTests κ) qs (by
    intro q _ hq
    have hn : q.pivot ≤ κ/2 ∧ Scalar.SignedIntervals.positiveMass q.gap ≤ κ ∧ negativeLogSum q.gap κ ≤ 1 := of_decide_eq_true hq
    simpa only [decide_eq_true_eq] using hn.1)
  simpa only [badPhaseCount,← decide_not,not_le] using hh

theorem ScheduleCut.strictLarge_count {κ B : ℝ} (hκ : 0 < κ) (hBκ : B < κ/2) (C : ScheduleCut)
    (hcap : ∀ b ∈ C.unselected, 0 < b → b ≤ B) :
    (strictLargeSteps κ C.word).length = (C.phases.filter fun q => decide (κ/2 < q.pivot)).length := by
  let w : ℝ → ℝ := fun b => if decide (κ/2 < b) then 1 else 0
  have hh := C.word_sum w
  have hz : (C.unselected.map w).sum = 0 := by
    apply list_weight_zero
    intro b hb
    have hn : ¬ κ/2 < b := by
      intro he
      have hb0 : 0 < b := (div_pos hκ (by norm_num)).trans he
      exact (not_lt_of_ge (hcap b hb hb0)) (hBκ.trans he)
    simp only [w,hn,decide_false,Bool.false_eq_true,↓reduceIte]
  rw [hz,zero_add] at hh
  have hw := list_filter_length_weight (fun b : ℝ => decide (κ/2 < b)) C.word
  have hp := list_filter_length_weight (fun q : CutPhase => decide (κ/2 < q.pivot)) C.phases
  have he : ((strictLargeSteps κ C.word).length : ℝ) = ((C.phases.filter fun q => decide (κ/2 < q.pivot)).length : ℝ) :=
    hw.trans (hh.trans hp.symm)
  exact_mod_cast he

theorem ScheduleCut.strictLarge_le_initial_marked {κ B : ℝ} (hκ : 0 < κ) (hBκ : B < κ/2) (C : ScheduleCut)
    (hcap : ∀ b ∈ C.unselected, 0 < b → b ≤ B) :
    (strictLargeSteps κ C.word).length ≤ badPhaseCount (initialPhaseTests κ) C.phases := by
  rw [C.strictLarge_count hκ hBκ hcap]
  exact strictLarge_pivots_le_initial_marked κ C.phases

end
end StrongSilver
