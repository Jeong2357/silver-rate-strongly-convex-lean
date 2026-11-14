-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

namespace StrongSilver

/-- Scan to the first good phase with a good buffer on its right.
The buffer may end at the terminal gap. -/
structure ReservedRun (α : Type*) where
  inside : List α
  remaining : List α

def reserveRun {α : Type*} (good : α → Bool) (buffer : ℕ) : List α → ReservedRun α
  | [] => ⟨[],[]⟩
  | q :: qs =>
    if good q && (qs.take buffer).all good then ⟨[],q::qs⟩
    else
      let R := reserveRun good buffer qs
      ⟨q::R.inside,R.remaining⟩

namespace ReservedRun
variable {α : Type*}

theorem partition (good : α → Bool) (buffer : ℕ) (qs : List α) :
    (reserveRun good buffer qs).inside ++ (reserveRun good buffer qs).remaining = qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [reserveRun]
    split
    · rfl
    · simpa only [List.cons_append] using congrArg (List.cons q) ih

theorem remaining_length_le (good : α → Bool) (buffer : ℕ) (qs : List α) :
    (reserveRun good buffer qs).remaining.length ≤ qs.length := by
  have hh := congrArg List.length (partition good buffer qs)
  simp only [List.length_append] at hh
  omega

theorem remaining_good (good : α → Bool) (buffer : ℕ) (qs : List α) :
    ∀ q rs, (reserveRun good buffer qs).remaining = q::rs →
      good q = true ∧ (rs.take buffer).all good = true := by
  induction qs with
  | nil => simp [reserveRun]
  | cons a qs ih =>
    simp only [reserveRun]
    split
    · rename_i hstop
      intro q rs he
      cases he
      simpa only [Bool.and_eq_true] using hstop
    · exact ih

theorem first_bad_consumed {good : α → Bool} {buffer : ℕ} {q : α} {qs : List α}
    (hq : good q = false) :
    (reserveRun good buffer (q::qs)).inside = q::(reserveRun good buffer qs).inside ∧
    (reserveRun good buffer (q::qs)).remaining = (reserveRun good buffer qs).remaining := by
  simp [reserveRun,hq]

theorem remaining_length_lt_of_first_bad {good : α → Bool} {buffer : ℕ} {q : α} {qs : List α}
    (hq : good q = false) : (reserveRun good buffer (q::qs)).remaining.length < (q::qs).length := by
  rw [(first_bad_consumed hq).2,List.length_cons]
  exact Nat.lt_succ_of_le (remaining_length_le good buffer qs)

end ReservedRun
end StrongSilver
