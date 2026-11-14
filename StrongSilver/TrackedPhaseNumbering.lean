-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScheduleCut

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1400000

def CutPhase.withIndex (q : CutPhase) (i : ℕ) : CutPhase := ⟨q.gap,q.pivot,i⟩

@[simp] theorem CutPhase.withIndex_gap (q : CutPhase) (i : ℕ) : (q.withIndex i).gap = q.gap := rfl
@[simp] theorem CutPhase.withIndex_pivot (q : CutPhase) (i : ℕ) : (q.withIndex i).pivot = q.pivot := rfl
@[simp] theorem CutPhase.withIndex_word (q : CutPhase) (i : ℕ) : (q.withIndex i).word = q.word := rfl

def numberTrackedPhases : ℕ → List CutPhase → List CutPhase
  | _,[] => []
  | i,q::qs => q.withIndex (i+q.gap.length)::numberTrackedPhases (i+q.word.length) qs

@[simp] theorem numberTrackedPhases_length (i : ℕ) (qs : List CutPhase) :
    (numberTrackedPhases i qs).length = qs.length := by
  induction qs generalizing i with
  | nil => rfl
  | cons q qs ih => simp only [numberTrackedPhases,List.length_cons,ih]

theorem numberTrackedPhases_word (i : ℕ) (qs : List CutPhase) :
    (numberTrackedPhases i qs).flatMap CutPhase.word = qs.flatMap CutPhase.word := by
  induction qs generalizing i with
  | nil => rfl
  | cons q qs ih => simp only [numberTrackedPhases,List.flatMap_cons,CutPhase.withIndex_word,ih]

theorem numberTrackedPhases_map {α : Type*} (f : CutPhase → α)
    (hf : ∀ q i, f (q.withIndex i) = f q) (i : ℕ) (qs : List CutPhase) :
    (numberTrackedPhases i qs).map f = qs.map f := by
  induction qs generalizing i with
  | nil => rfl
  | cons q qs ih => simp only [numberTrackedPhases,List.map_cons,hf,ih]

end
end StrongSilver
