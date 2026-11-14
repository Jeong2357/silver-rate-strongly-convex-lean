-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScheduleCut

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

namespace ScheduleCut

def prependGap (C : ScheduleCut) : List ℝ → ScheduleCut
  | [] => C
  | a::h => (C.prependGap h).prependUnselected a

theorem prependGap_selected (C : ScheduleCut) (i : ℕ) (b : ℝ) (h : List ℝ) :
    (C.prependSelected i b).prependGap h = ⟨⟨h,b,i⟩::C.phases,C.terminal⟩ := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [prependGap,ih,prependUnselected]

def concat (C D : ScheduleCut) : ScheduleCut :=
  ⟨C.phases++(D.prependGap C.terminal).phases,(D.prependGap C.terminal).terminal⟩

theorem concat_prependSelected (C D : ScheduleCut) (i : ℕ) (a : ℝ) :
    (C.prependSelected i a).concat D = (C.concat D).prependSelected i a := by
  rfl

theorem concat_prependUnselected (C D : ScheduleCut) (a : ℝ) :
    (C.prependUnselected a).concat D = (C.concat D).prependUnselected a := by
  rcases C with ⟨qs,t⟩
  cases qs with
  | nil => rfl
  | cons q qs => rfl

theorem concat_before_selected (C D : ScheduleCut) (i : ℕ) (b : ℝ) :
    C.concat (D.prependSelected i b) = ⟨C.phases++(⟨C.terminal,b,i⟩::D.phases),D.terminal⟩ := by
  simp only [concat,prependGap_selected]

end ScheduleCut

/-- Exact cut concatenation retains the unfinished terminal gap and adds
it to the next phase, rather than inserting a boundary into the schedule. -/
theorem cutScheduleFrom_append (choose : ℕ → ℝ → Bool) (i : ℕ) (h k : List ℝ) :
    cutScheduleFrom choose i (h++k) =
      (cutScheduleFrom choose i h).concat (cutScheduleFrom choose (i+h.length) k) := by
  induction h generalizing i with
  | nil => simp only [List.nil_append,List.length_nil,Nat.add_zero,cutScheduleFrom,ScheduleCut.concat,ScheduleCut.prependGap,List.nil_append]
  | cons a h ih =>
    have hi : i+(a::h).length = (i+1)+h.length := by simp only [List.length_cons]; omega
    simp only [List.cons_append,cutScheduleFrom]
    by_cases hc : choose i a = true
    · simp only [hc,↓reduceIte,ih,hi,ScheduleCut.concat_prependSelected]
    · have hfalse := Bool.eq_false_iff.mpr hc
      simp only [hfalse,Bool.false_eq_true,↓reduceIte,ih,hi,ScheduleCut.concat_prependUnselected]

end
end StrongSilver
