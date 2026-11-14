-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Tactic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

/-- Splitting a signed word at its largest positive entry, taking its
first occurrence, preserves every original entry on the two sides. -/
theorem first_maximum_split (h : List ℝ) (hp : ∃ b ∈ h, 0 < b) :
    ∃ left : List ℝ, ∃ b : ℝ, ∃ right : List ℝ,
      h = left++b::right ∧ 0 < b ∧ (∀ x ∈ left, x < b) ∧ (∀ x ∈ right, x ≤ b) := by
  induction h with
  | nil => simp at hp
  | cons a h ih =>
    by_cases ht : ∃ b ∈ h, 0 < b
    · obtain ⟨left,b,right,he,hb,hl,hr⟩ := ih ht
      have hall (x : ℝ) (hx : x ∈ h) : x ≤ b := by
        rw [he] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact (hl x hx).le
        · rcases List.mem_cons.mp hx with hx | hx
          · subst x; exact le_rfl
          · exact hr x hx
      by_cases ha : a < b
      · refine ⟨a::left,b,right,?_,hb,?_,hr⟩
        · simpa only [List.cons_append] using congrArg (List.cons a) he
        · intro x hx
          rcases List.mem_cons.mp hx with hx | hx
          · subst x; exact ha
          · exact hl x hx
      · refine ⟨[],a,h,rfl,hb.trans_le (le_of_not_gt ha),by simp,?_⟩
        exact fun x hx => (hall x hx).trans (le_of_not_gt ha)
    · have ha : 0 < a := by
        obtain ⟨b,hb,hbp⟩ := hp
        rcases List.mem_cons.mp hb with hb | hb
        · simpa only [hb] using hbp
        · exact False.elim (ht ⟨b,hb,hbp⟩)
      refine ⟨[],a,h,rfl,ha,by simp,?_⟩
      intro x hx
      have hxn : x ≤ 0 := le_of_not_gt (fun hxp => ht ⟨x,hx,hxp⟩)
      exact hxn.trans ha.le

end
end StrongSilver
