-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutInsertionPrefix

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

theorem cutScheduleFrom_congr {choose other : ℕ → ℝ → Bool} (i : ℕ) (h : List ℝ)
    (he : ∀ j a, i ≤ j → j < i+h.length → choose j a = other j a) :
    cutScheduleFrom choose i h = cutScheduleFrom other i h := by
  induction h generalizing i with
  | nil => rfl
  | cons a h ih =>
    have hhead := he i a le_rfl (by simp)
    have htail := ih (i+1) (by
      intro j b hlo hhi
      apply he j b (by omega)
      simp only [List.length_cons] at ⊢
      omega)
    simp only [cutScheduleFrom,hhead,htail]

def selectIndex (choose : ℕ → ℝ → Bool) (p : ℕ) (j : ℕ) (a : ℝ) : Bool :=
  if j = p then true else choose j a

theorem cutScheduleFrom_selectIndex_after (choose : ℕ → ℝ → Bool) {p i : ℕ} (hpi : p < i) (h : List ℝ) :
    cutScheduleFrom (selectIndex choose p) i h = cutScheduleFrom choose i h := by
  apply cutScheduleFrom_congr
  intro j a hlo _
  simp only [selectIndex,if_neg (by omega : j ≠ p)]

/-- Turning on any one unselected original position is an actual gap
split, with the original chronological index and the same full schedule. -/
theorem exists_selector_insertion (choose : ℕ → ℝ → Bool) (i : ℕ) (h : List ℝ) (p : ℕ)
    (hp : p < h.length) (hfalse : choose (i+p) h[p] = false) :
    ∃ I : CutInsertion, I.oldCut = cutScheduleFrom choose i h ∧
      I.newCut = cutScheduleFrom (selectIndex choose (i+p)) i h ∧ I.pivot = h[p] := by
  induction h generalizing i p with
  | nil => simp at hp
  | cons a h ih =>
    cases p with
    | zero =>
      have hf : choose i a = false := by simpa only [Nat.add_zero,List.getElem_cons_zero] using hfalse
      let C := cutScheduleFrom choose (i+1) h
      obtain ⟨I,ho,hn,hpiv⟩ := CutInsertion.exists_first_insertion C a i
      have htail : cutScheduleFrom (selectIndex choose i) (i+1) h = C := cutScheduleFrom_selectIndex_after choose (Nat.lt_succ_self i) h
      refine ⟨I,?_,?_,hpiv⟩
      · rw [ho]
        simp only [cutScheduleFrom,hf,Bool.false_eq_true,↓reduceIte,C]
      · simp only [Nat.add_zero]
        rw [hn]
        simp only [cutScheduleFrom,selectIndex,if_pos rfl,↓reduceIte] at ⊢
        change C.prependSelected i a = (cutScheduleFrom (selectIndex choose i) (i+1) h).prependSelected i a
        rw [htail]
    | succ p =>
      have hplen : p < h.length := by simp only [List.length_cons] at hp; omega
      have htarget : i+(p+1) = (i+1)+p := by omega
      have hf : choose ((i+1)+p) h[p] = false := by
        simpa only [Nat.succ_eq_add_one,htarget,List.getElem_cons_succ] using hfalse
      obtain ⟨I,ho,hn,hpiv⟩ := ih (i+1) p hplen hf
      have hhead : selectIndex choose (i+(p+1)) i a = choose i a := by
        simp only [selectIndex,if_neg (by omega : i ≠ i+(p+1))]
      let J := if choose i a then I.prependSelected i a else I.prependUnselected a
      have hnew : cutScheduleFrom (selectIndex choose (i+(p+1))) i (a::h) =
          if choose i a then (cutScheduleFrom (selectIndex choose ((i+1)+p)) (i+1) h).prependSelected i a
          else (cutScheduleFrom (selectIndex choose ((i+1)+p)) (i+1) h).prependUnselected a := by
        rw [cutScheduleFrom,hhead,htarget]
      refine ⟨J,?_,?_,?_⟩
      · cases hh : choose i a <;> simp only [J,hh,Bool.false_eq_true,↓reduceIte,
          CutInsertion.oldCut_prependSelected,CutInsertion.oldCut_prependUnselected,ho,cutScheduleFrom,hh]
      · rw [hnew]
        cases hh : choose i a <;> simp only [J,hh,Bool.false_eq_true,↓reduceIte,
          CutInsertion.newCut_prependSelected,CutInsertion.newCut_prependUnselected,hn]
      · cases hh : choose i a <;> simp only [J,hh,Bool.false_eq_true,↓reduceIte,
          CutInsertion.pivot_prependSelected,CutInsertion.pivot_prependUnselected,hpiv,List.getElem_cons_succ]

end
end StrongSilver
