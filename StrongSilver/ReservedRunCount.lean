-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReservedRun
import Mathlib.Data.List.Induction

namespace StrongSilver

def badPhaseCount {α : Type*} (good : α → Bool) (qs : List α) : ℕ :=
  (qs.filter fun q => !good q).length

@[simp] theorem badPhaseCount_nil {α : Type*} (good : α → Bool) : badPhaseCount good [] = 0 := rfl

theorem badPhaseCount_cons {α : Type*} (good : α → Bool) (q : α) (qs : List α) :
    badPhaseCount good (q::qs) = (if good q then 0 else 1)+badPhaseCount good qs := by
  cases hq : good q <;> simp [badPhaseCount,hq,Nat.add_comm]

theorem badPhaseCount_append {α : Type*} (good : α → Bool) (qs rs : List α) :
    badPhaseCount good (qs++rs) = badPhaseCount good qs+badPhaseCount good rs := by
  simp [badPhaseCount,List.filter_append]

theorem reserveRun_bad_partition {α : Type*} (good : α → Bool) (buffer : ℕ) (qs : List α) :
    badPhaseCount good (reserveRun good buffer qs).inside+badPhaseCount good (reserveRun good buffer qs).remaining =
      badPhaseCount good qs := by
  rw [← badPhaseCount_append,ReservedRun.partition]

/-- Merging across one good phase consumes at most two phases per marked
phase, before reserving the two separate neighboring roles. -/
theorem reserveRun_one_size {α : Type*} (good : α → Bool) (qs : List α) :
    (reserveRun good 1 qs).inside.length ≤ 2*badPhaseCount good (reserveRun good 1 qs).inside := by
  induction qs using List.twoStepInduction with
  | nil => simp [reserveRun]
  | singleton q =>
    cases hq : good q <;> simp [reserveRun,hq,badPhaseCount]
  | cons_cons q r qs ih ihrest =>
    cases hq : good q
    · have hh := ihrest r
      rw [(ReservedRun.first_bad_consumed hq).1]
      simp only [List.length_cons,badPhaseCount_cons,hq,Bool.false_eq_true,↓reduceIte]
      omega
    · cases hr : good r
      · have he : (reserveRun good 1 (q::r::qs)).inside = q::r::(reserveRun good 1 qs).inside := by
          simp [reserveRun,hq,hr]
        rw [he]
        simp only [List.length_cons,badPhaseCount_cons,hq,hr,Bool.false_eq_true,↓reduceIte,zero_add]
        omega
      · simp [reserveRun,hq,hr]

theorem reserveRun_bad_nonempty {α : Type*} {good : α → Bool} {q : α} {qs : List α}
    (hq : good q = false) (buffer : ℕ) : 1 ≤ badPhaseCount good (reserveRun good buffer (q::qs)).inside := by
  rw [(ReservedRun.first_bad_consumed hq).1,badPhaseCount_cons]
  simp [hq]

theorem reserveRun_one_reserved_size {α : Type*} {good : α → Bool} {q : α} {qs : List α}
    (hq : good q = false) :
    (reserveRun good 1 (q::qs)).inside.length+2 ≤ 4*badPhaseCount good (reserveRun good 1 (q::qs)).inside := by
  have hs := reserveRun_one_size good (q::qs)
  have hb := reserveRun_bad_nonempty (qs := qs) hq 1
  omega

end StrongSilver
