-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Data.List.Enum
import Mathlib.Data.Real.Basic

namespace StrongSilver
noncomputable section

/-- A gap and its selected right endpoint, in the original order of the schedule. -/
structure CutPhase where
  gap : List ℝ
  pivot : ℝ
  index : ℕ

namespace CutPhase
def word (q : CutPhase) : List ℝ := q.gap ++ [q.pivot]
end CutPhase

/-- The terminal gap has no selected right endpoint. -/
structure ScheduleCut where
  phases : List CutPhase
  terminal : List ℝ

namespace ScheduleCut

def word (C : ScheduleCut) : List ℝ := C.phases.flatMap CutPhase.word ++ C.terminal
def selected (C : ScheduleCut) : List (ℕ × ℝ) := C.phases.map fun q => (q.index,q.pivot)
def gaps (C : ScheduleCut) : List (List ℝ) := C.phases.map CutPhase.gap ++ [C.terminal]
def unselected (C : ScheduleCut) : List ℝ := C.gaps.flatten

def prependSelected (C : ScheduleCut) (i : ℕ) (a : ℝ) : ScheduleCut :=
  ⟨⟨[],a,i⟩ :: C.phases,C.terminal⟩

def prependUnselected (C : ScheduleCut) (a : ℝ) : ScheduleCut :=
  match C.phases with
  | [] => ⟨[],a :: C.terminal⟩
  | q :: qs => ⟨{q with gap := a :: q.gap} :: qs,C.terminal⟩

@[simp] theorem word_prependSelected (C : ScheduleCut) (i : ℕ) (a : ℝ) :
    (C.prependSelected i a).word = a :: C.word := by
  simp [prependSelected,word,CutPhase.word]

@[simp] theorem word_prependUnselected (C : ScheduleCut) (a : ℝ) :
    (C.prependUnselected a).word = a :: C.word := by
  cases C with
  | mk qs t => cases qs <;> simp [prependUnselected,word,CutPhase.word,List.append_assoc]

@[simp] theorem selected_prependSelected (C : ScheduleCut) (i : ℕ) (a : ℝ) :
    (C.prependSelected i a).selected = (i,a) :: C.selected := by
  simp [prependSelected,selected]

@[simp] theorem selected_prependUnselected (C : ScheduleCut) (a : ℝ) :
    (C.prependUnselected a).selected = C.selected := by
  cases C with
  | mk qs t => cases qs <;> simp [prependUnselected,selected]

@[simp] theorem unselected_prependSelected (C : ScheduleCut) (i : ℕ) (a : ℝ) :
    (C.prependSelected i a).unselected = C.unselected := by
  simp [prependSelected,unselected,gaps]

@[simp] theorem unselected_prependUnselected (C : ScheduleCut) (a : ℝ) :
    (C.prependUnselected a).unselected = a :: C.unselected := by
  cases C with
  | mk qs t => cases qs <;> simp [prependUnselected,unselected,gaps,List.append_assoc]

theorem mem_gap_unselected {C : ScheduleCut} {q : CutPhase} (hq : q ∈ C.phases)
    {a : ℝ} (ha : a ∈ q.gap) : a ∈ C.unselected := by
  simp only [unselected,List.mem_flatten]
  exact ⟨q.gap, List.mem_append_left _ (List.mem_map.mpr ⟨q,hq,rfl⟩),ha⟩

theorem mem_terminal_unselected {C : ScheduleCut} {a : ℝ} (ha : a ∈ C.terminal) :
    a ∈ C.unselected := by
  simp only [unselected,List.mem_flatten]
  exact ⟨C.terminal,List.mem_append_right _ (by simp [gaps]),ha⟩

end ScheduleCut

/-- Select actual positions; the index permits a partial initial segment of a tie. -/
def cutScheduleFrom (choose : ℕ → ℝ → Bool) : ℕ → List ℝ → ScheduleCut
  | _, [] => ⟨[],[]⟩
  | i, a :: h =>
    let C := cutScheduleFrom choose (i+1) h
    if choose i a then C.prependSelected i a else C.prependUnselected a

def cutSchedule (choose : ℕ → ℝ → Bool) (h : List ℝ) : ScheduleCut := cutScheduleFrom choose 0 h

theorem cutScheduleFrom_word (choose : ℕ → ℝ → Bool) (i : ℕ) (h : List ℝ) :
    (cutScheduleFrom choose i h).word = h := by
  induction h generalizing i with
  | nil => rfl
  | cons a h ih =>
    simp only [cutScheduleFrom]
    split <;> simp [ih]

@[simp] theorem cutSchedule_word (choose : ℕ → ℝ → Bool) (h : List ℝ) :
    (cutSchedule choose h).word = h := cutScheduleFrom_word choose 0 h

theorem cutScheduleFrom_selected (choose : ℕ → ℝ → Bool) (i : ℕ) (h : List ℝ) :
    (cutScheduleFrom choose i h).selected = ((h.zipIdx i).map Prod.swap).filter (fun z => choose z.1 z.2) := by
  induction h generalizing i with
  | nil => rfl
  | cons a h ih =>
    simp only [cutScheduleFrom,List.zipIdx_cons,List.map_cons,List.filter_cons,Prod.swap_prod_mk]
    split <;> simp_all

theorem cutScheduleFrom_selected_property {choose : ℕ → ℝ → Bool} {i : ℕ} {h : List ℝ}
    {q : CutPhase} (hq : q ∈ (cutScheduleFrom choose i h).phases) : choose q.index q.pivot = true := by
  have hh : (q.index,q.pivot) ∈ (cutScheduleFrom choose i h).selected :=
    List.mem_map.mpr ⟨q,hq,rfl⟩
  rw [cutScheduleFrom_selected] at hh
  exact (List.mem_filter.mp hh).2

theorem cutScheduleFrom_unselected_property {choose : ℕ → ℝ → Bool} (P : ℝ → Prop)
    (hP : ∀ i a, choose i a = false → P a) (i : ℕ) (h : List ℝ) :
    ∀ a ∈ (cutScheduleFrom choose i h).unselected, P a := by
  induction h generalizing i with
  | nil => simp [cutScheduleFrom,ScheduleCut.unselected,ScheduleCut.gaps]
  | cons a h ih =>
    simp only [cutScheduleFrom]
    split
    · simpa only [ScheduleCut.unselected_prependSelected] using ih (i+1)
    · rename_i hn
      have hn' : choose i a = false := Bool.eq_false_iff.mpr hn
      simpa only [ScheduleCut.unselected_prependUnselected,List.mem_cons,forall_eq_or_imp] using
        And.intro (hP i a hn') (ih (i+1))

def fullCut (A : ℝ) (h : List ℝ) : ScheduleCut := cutSchedule (fun _ a => decide (A < a)) h
def closedCut (A : ℝ) (h : List ℝ) : ScheduleCut := cutSchedule (fun _ a => decide (A ≤ a)) h
def partialTieCut (A : ℝ) (tieTop : ℕ) (h : List ℝ) : ScheduleCut :=
  cutSchedule (fun i a => decide (A < a ∨ a = A ∧ i < tieTop)) h

theorem fullCut_pivot {A : ℝ} {h : List ℝ} {q : CutPhase} (hq : q ∈ (fullCut A h).phases) : A < q.pivot := by
  exact of_decide_eq_true (cutScheduleFrom_selected_property hq)

theorem closedCut_pivot {A : ℝ} {h : List ℝ} {q : CutPhase} (hq : q ∈ (closedCut A h).phases) : A ≤ q.pivot := by
  exact of_decide_eq_true (cutScheduleFrom_selected_property hq)

theorem partialTieCut_pivot {A : ℝ} {h : List ℝ} {tieTop : ℕ} {q : CutPhase}
    (hq : q ∈ (partialTieCut A tieTop h).phases) : A ≤ q.pivot := by
  have hh := of_decide_eq_true (cutScheduleFrom_selected_property hq)
  rcases hh with hh | ⟨hh,_⟩
  · exact hh.le
  · exact hh.ge

theorem fullCut_unselected {A : ℝ} {h : List ℝ} {a : ℝ} (ha : a ∈ (fullCut A h).unselected) : a ≤ A := by
  exact cutScheduleFrom_unselected_property (fun a => a ≤ A) (by simpa using fun _ a => le_of_not_gt (a := A) (b := a)) 0 h a ha

theorem partialTieCut_unselected {A : ℝ} {h : List ℝ} {tieTop : ℕ} {a : ℝ}
    (ha : a ∈ (partialTieCut A tieTop h).unselected) : a ≤ A := by
  apply cutScheduleFrom_unselected_property (fun a => a ≤ A) ?_ 0 h a ha
  intro i a hh
  have hn : ¬ (A < a ∨ a = A ∧ i < tieTop) := of_decide_eq_false hh
  exact le_of_not_gt (fun he => hn (Or.inl he))

end
end StrongSilver
