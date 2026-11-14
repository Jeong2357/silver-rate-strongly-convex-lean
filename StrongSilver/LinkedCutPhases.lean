-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFrontier
import StrongSilver.BandCutTrees

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 6200000

namespace LinkedGap

def phase? (q : LinkedGap) : Option CutPhase :=
  q.following.map fun p => ⟨q.node.source.word,p.pivot,p.pivotIndex⟩

end LinkedGap
namespace ScheduleTree

/-- Exact correspondence with the original full-cut phases, including
the original selected indices. The external terminal boundary is only
attached when it actually exists. -/
theorem linkedFrontier_cut_phases (φ : ℝ → ℝ) (hφ : Monotone φ) (s : ℝ) (hzero : φ 0 ≤ s)
    (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree) (hc : t.Cartesian) :
    ((linkedFrontier φ s start κ parent following t).filterMap LinkedGap.phase?) =
      (cutScheduleFrom (fun _ b => decide (s < φ b)) start t.word).phases++
        following.toList.map (fun p => (⟨(cutScheduleFrom (fun _ b => decide (s < φ b)) start t.word).terminal,p.pivot,p.pivotIndex⟩ : CutPhase)) := by
  induction t generalizing start κ parent following with
  | leaf word =>
    have hn : ∀ b ∈ word, ∀ j : ℕ, decide (s < φ b) = false := by
      intro b hb j
      exact decide_eq_false (not_lt_of_ge ((hφ (hc b hb)).trans hzero))
    rw [ScheduleTree.word,cutScheduleFrom_none _ start word hn]
    cases following <;> simp [linkedFrontier,LinkedGap.phase?,ScheduleTree.word]
  | split l b r il ir =>
    by_cases hb : s < φ b
    · rw [linkedFrontier,if_pos hb,List.filterMap_append,il start 0 _ _ hc.1,ir _ κ _ _ hc.2.1]
      rw [word,cutScheduleFrom_append]
      simp only [cutScheduleFrom,decide_eq_true hb,↓reduceIte,ScheduleCut.concat_before_selected]
      simp only [Option.toList_some,List.map_cons,List.map_nil,ScheduleNode.pivot,ScheduleNode.pivotIndex,rootStep_split]
      simp only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
    · have hn : ∀ x ∈ (ScheduleTree.split l b r).word, ∀ j : ℕ, decide (s < φ x) = false := by
        intro x hx j
        exact decide_eq_false (not_lt_of_ge ((hφ (split_word_le hc x hx)).trans (le_of_not_gt hb)))
      rw [cutScheduleFrom_none _ start _ hn,linkedFrontier,if_neg hb]
      cases following <;> simp [LinkedGap.phase?]

end ScheduleTree

open ScheduleTree Real Filter Set

theorem eventually_band_linked_cut_phases : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y : ℝ, ∀ h : List ℝ,
    1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    ((linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h)).filterMap LinkedGap.phase?) =
      (bandFullCut μ u y h).phases := by
  filter_upwards [eventually_outer_band_log_window] with u H
  intro κ B μ y h hB hU hμ hμB hy
  have W := H B μ y hB hU hμ hμB hy
  have hφ := cappedStep_monotone (B:=B) hμ (by linarith only [hμB])
  have hzero : cappedStep μ B 0 ≤ bandPad u+Real.exp y := by
    rw [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero]
    exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hh := linkedFrontier_cut_phases (cappedStep μ B) hφ (bandPad u+Real.exp y) hzero 0 κ none none (cartesian h) (cartesian_valid h)
  simp only [Option.toList_none,List.map_nil,List.append_nil,cartesian_word] at hh
  have hCut := band_heightCut_eq hμ (by linarith only [hμB]) W.2.2.2.2.2.2.2.2.2.2 h
  change _ = (heightCut (cappedStep μ B) (bandPad u) y h).phases at hh
  rw [hCut] at hh
  exact hh

end
end StrongSilver
