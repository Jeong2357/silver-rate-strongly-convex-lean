-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianThresholdCut
import StrongSilver.CutMasses
import StrongSilver.PaddedGapSplit

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3200000

theorem cut_log_concat_selected (φ : ℝ → ℝ) (P κ : ℝ) (C D : ScheduleCut) (i : ℕ) (b : ℝ) :
    cutLogProduct φ P κ (C.concat (D.prependSelected i b)) =
      cutLogProduct φ P 0 C+cutLogProduct φ P κ D-Real.log (φ b-P) := by
  rw [ScheduleCut.concat_before_selected]
  simp only [cutLogProduct,cutMasses,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
    List.map_nil,List.sum_nil,List.map_map,Function.comp_def,add_zero]
  ring

theorem cut_power_concat_selected (φ : ℝ → ℝ) (P κ : ℝ) (C D : ScheduleCut) (i : ℕ) (b : ℝ) :
    cutPower φ P κ (C.concat (D.prependSelected i b)) = cutPower φ P 0 C+cutPower φ P κ D := by
  rw [ScheduleCut.concat_before_selected]
  simp only [cutPower,cutMasses,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
    List.map_nil,List.sum_nil,List.map_map,Function.comp_def,add_zero]
  ring

namespace ScheduleTree

def paddedRootGain (φ : ℝ → ℝ) (P κ : ℝ) : ScheduleTree → ℝ
  | .leaf _ => 0
  | .split l b r => splitGain (gapPrefix φ l.word+P) (gapPrefix φ r.word+P+κ)
      (φ b-P) (gapPrefix φ (l.word++b::r.word)+P+κ)

def paddedRootDecrease (φ : ℝ → ℝ) (P κ : ℝ) : ScheduleTree → ℝ
  | .leaf _ => 0
  | .split l b r => powerDecrease (gapPrefix φ l.word+P) (gapPrefix φ r.word+P+κ)
      (gapPrefix φ (l.word++b::r.word)+P+κ)

/-- The terminal reserve follows the right child at every split. -/
def splitSumAbove (F : ℝ → ScheduleTree → ℝ) (A κ : ℝ) : ScheduleTree → ℝ
  | .leaf _ => 0
  | .split l b r => if A < b then F κ (.split l b r)+splitSumAbove F A 0 l+splitSumAbove F A κ r else 0

theorem paddedRootGain_log {φ : ℝ → ℝ} {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ)
    (l r : ScheduleTree) (b : ℝ) (hb : P < φ b) :
    paddedRootGain φ P κ (.split l b r) =
      Real.log (gapPrefix φ (l.word++b::r.word)+P+κ)-Real.log (gapPrefix φ l.word+P)-
        Real.log (gapPrefix φ r.word+P+κ)+Real.log (φ b-P) := by
  have hl : 0 < gapPrefix φ l.word+P := add_pos_of_nonneg_of_pos (gapPrefix_nonnegative φ _) hP
  have hr : 0 < gapPrefix φ r.word+P+κ := by linarith only [gapPrefix_nonnegative φ r.word,hP,hκ]
  have hz : 0 < gapPrefix φ (l.word++b::r.word)+P+κ := by
    linarith only [gapPrefix_nonnegative φ (l.word++b::r.word),hP,hκ]
  have ht := sub_pos.mpr hb
  rw [paddedRootGain,splitGain,Real.log_div (mul_pos ht hz).ne' (mul_pos hl hr).ne',
    Real.log_mul ht.ne' hz.ne',Real.log_mul hl.ne' hr.ne']
  ring

/-- Exact full-cut logarithmic step function, including all ties and
the rightmost terminal reserve. Its jumps are the concrete padded gains. -/
theorem full_cut_log_jump_formula {φ : ℝ → ℝ} {P κ A : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ)
    (hA : 0 ≤ A) (t : ScheduleTree) (hc : t.Cartesian)
    (hφ : ∀ b ∈ t.word, A < b → P < φ b) (i : ℕ) :
    cutLogProduct φ P κ (cutScheduleFrom (fun _ b => decide (A < b)) i t.word) =
      Real.log (gapPrefix φ t.word+P+κ)-splitSumAbove (fun κ s => paddedRootGain φ P κ s) A κ t := by
  induction t generalizing κ i with
  | leaf hw =>
    have hn : ∀ b ∈ hw, ∀ j : ℕ, decide (A < b) = false := fun b hb _ =>
      decide_eq_false (not_lt_of_ge ((hc b hb).trans hA))
    rw [word,cutScheduleFrom_none _ i hw hn]
    simp [cutLogProduct,cutMasses,splitSumAbove,word]
  | split l b r il ir =>
    by_cases hb : A < b
    · have hφb := hφ b (by simp [word]) hb
      have hφl : ∀ x ∈ l.word, A < x → P < φ x := fun x hx => hφ x ((left_word_sublist l r b).subset hx)
      have hφr : ∀ x ∈ r.word, A < x → P < φ x := fun x hx => hφ x ((right_word_sublist l r b).subset hx)
      rw [word,cutScheduleFrom_append]
      simp only [cutScheduleFrom,decide_eq_true hb,↓reduceIte]
      rw [cut_log_concat_selected,il (κ := 0) (by norm_num) hc.1 hφl,ir hκ hc.2.1 hφr]
      simp only [splitSumAbove,if_pos hb,word]
      rw [paddedRootGain_log hP hκ l r b hφb]
      ring
    · have hn : ∀ x ∈ (ScheduleTree.split l b r).word, ∀ j : ℕ, decide (A < x) = false := by
        intro x hx _
        exact decide_eq_false (not_lt_of_ge ((split_word_le hc x hx).trans (le_of_not_gt hb)))
      rw [cutScheduleFrom_none _ i _ hn]
      simp [cutLogProduct,cutMasses,splitSumAbove,hb]

/-- Exact full-cut power step function with the same original splits. -/
theorem full_cut_power_jump_formula {φ : ℝ → ℝ} {P κ A : ℝ} (hA : 0 ≤ A)
    (t : ScheduleTree) (hc : t.Cartesian) (i : ℕ) :
    cutPower φ P κ (cutScheduleFrom (fun _ b => decide (A < b)) i t.word) =
      (gapPrefix φ t.word+P+κ)^nu-splitSumAbove (fun κ s => paddedRootDecrease φ P κ s) A κ t := by
  induction t generalizing κ i with
  | leaf hw =>
    have hn : ∀ b ∈ hw, ∀ j : ℕ, decide (A < b) = false := fun b hb _ =>
      decide_eq_false (not_lt_of_ge ((hc b hb).trans hA))
    rw [word,cutScheduleFrom_none _ i hw hn]
    simp [cutPower,cutMasses,splitSumAbove,word]
  | split l b r il ir =>
    by_cases hb : A < b
    · rw [word,cutScheduleFrom_append]
      simp only [cutScheduleFrom,decide_eq_true hb,↓reduceIte]
      rw [cut_power_concat_selected,il hc.1,ir hc.2.1]
      simp only [splitSumAbove,if_pos hb,word,paddedRootDecrease,powerDecrease,add_zero]
      ring
    · have hn : ∀ x ∈ (ScheduleTree.split l b r).word, ∀ j : ℕ, decide (A < x) = false := by
        intro x hx _
        exact decide_eq_false (not_lt_of_ge ((split_word_le hc x hx).trans (le_of_not_gt hb)))
      rw [cutScheduleFrom_none _ i _ hn]
      simp [cutPower,cutMasses,splitSumAbove,hb]

end ScheduleTree
end
end StrongSilver
