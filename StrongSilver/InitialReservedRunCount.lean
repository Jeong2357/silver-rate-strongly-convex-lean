-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReservedRunCount

namespace StrongSilver
set_option maxHeartbeats 1600000

/-- Merging across at most three good phases consumes at most four phases
per marked phase, before adding the separate neighboring roles. -/
theorem reserveRun_three_size {α : Type*} (good : α → Bool) (qs : List α) :
    (reserveRun good 3 qs).inside.length ≤ 4*badPhaseCount good (reserveRun good 3 qs).inside := by
  have aux : ∀ n : ℕ, ∀ xs : List α, xs.length ≤ n →
      (reserveRun good 3 xs).inside.length ≤ 4*badPhaseCount good (reserveRun good 3 xs).inside := by
    intro n
    induction n with
    | zero =>
      intro xs hlen
      have he : xs = [] := List.length_eq_zero_iff.mp (by omega)
      simp [he,reserveRun]
    | succ n ih =>
      intro xs hlen
      cases xs with
      | nil => simp [reserveRun]
      | cons q xs =>
        cases hq : good q
        · have ht := ih xs (by simp only [List.length_cons] at hlen; omega)
          rw [(ReservedRun.first_bad_consumed hq).1]
          simp only [List.length_cons,badPhaseCount_cons,hq,Bool.false_eq_true,↓reduceIte]
          omega
        · cases xs with
          | nil => simp [reserveRun,hq]
          | cons r xs =>
            cases hr : good r
            · have ht := ih xs (by simp only [List.length_cons] at hlen; omega)
              have he : (reserveRun good 3 (q::r::xs)).inside = q::r::(reserveRun good 3 xs).inside := by
                simp [reserveRun,hq,hr]
              rw [he]
              simp only [List.length_cons,badPhaseCount_cons,hq,hr,Bool.false_eq_true,↓reduceIte,zero_add]
              omega
            · cases xs with
              | nil => simp [reserveRun,hq,hr]
              | cons c xs =>
                cases hc : good c
                · have ht := ih xs (by simp only [List.length_cons] at hlen; omega)
                  have he : (reserveRun good 3 (q::r::c::xs)).inside = q::r::c::(reserveRun good 3 xs).inside := by
                    simp [reserveRun,hq,hr,hc]
                  rw [he]
                  simp only [List.length_cons,badPhaseCount_cons,hq,hr,hc,Bool.false_eq_true,↓reduceIte,zero_add]
                  omega
                · cases xs with
                  | nil => simp [reserveRun,hq,hr,hc]
                  | cons d xs =>
                    cases hd : good d
                    · have ht := ih xs (by simp only [List.length_cons] at hlen; omega)
                      have he : (reserveRun good 3 (q::r::c::d::xs)).inside = q::r::c::d::(reserveRun good 3 xs).inside := by
                        simp [reserveRun,hq,hr,hc,hd]
                      rw [he]
                      simp only [List.length_cons,badPhaseCount_cons,hq,hr,hc,hd,Bool.false_eq_true,↓reduceIte,zero_add]
                      omega
                    · simp [reserveRun,hq,hr,hc,hd]
  exact aux qs.length qs le_rfl

theorem reserveRun_three_reserved_size {α : Type*} {good : α → Bool} {q : α} {qs : List α}
    (hq : good q = false) :
    (reserveRun good 3 (q::qs)).inside.length+3 ≤ 7*badPhaseCount good (reserveRun good 3 (q::qs)).inside := by
  have hs := reserveRun_three_size good (q::qs)
  have hb := reserveRun_bad_nonempty (qs := qs) hq 3
  omega

end StrongSilver
