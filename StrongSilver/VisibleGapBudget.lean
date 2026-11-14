-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ParentedScheduleNodes
import StrongSilver.IndexedFrontierProperties
import StrongSilver.IndexedGapObservables
import StrongSilver.SingleGapRefinement
import StrongSilver.ReservedNodeTransform

namespace StrongSilver
open ScheduleTree ParentedScheduleNode
noncomputable section
set_option maxHeartbeats 3600000

local instance (φ : ℝ → ℝ) (s : ℝ) (q : ParentedScheduleNode) : Decidable (q.Visible φ s) := Classical.propDecidable _

/-- The nonnegative quantity charged to an actual visible gap. The
single-root competitor is eligible at its original absolute position. -/
def visibleNodeScore (φ : ℝ → ℝ) (P price : ℝ) (eligible : ℕ → ℝ → Bool) (q : ScheduleNode) : ℝ :=
  if P < φ q.pivot ∧ eligible q.pivotIndex q.pivot = true then
    max (paddedRootGain φ P q.reserve q.source-price) 0+gapLogDeficit φ P q.reserve q.source.word
  else 0

theorem visibleNodeScore_le_gap (φ : ℝ → ℝ) {P : ℝ} (hP : 0 < P) (hzero : φ 0 ≤ P)
    (price : ℝ) (eligible : ℕ → ℝ → Bool) (q : ScheduleNode) (hκ : 0 ≤ q.reserve) :
    visibleNodeScore φ P price eligible q ≤
      gapSavingsMaximum φ P q.reserve price q.start q.source.word eligible+gapLogDeficit φ P q.reserve q.source.word := by
  have hR := gapSavingsMaximum_nonnegative φ P q.reserve price q.start q.source.word eligible
  have hDef := gapLogDeficit_nonnegative φ hP hκ q.source.word
  unfold visibleNodeScore
  split_ifs with hq
  · cases hs : q.source with
    | leaf hw =>
      have hs0 : q.pivot = 0 := by simp only [ScheduleNode.pivot,hs,rootStep]
      have hh := hq.1
      rw [hs0] at hh
      exact False.elim (not_lt_of_ge hzero hh)
    | split l b r =>
      have hb : P < φ b := by simpa only [ScheduleNode.pivot,hs,rootStep] using hq.1
      have he : eligible (q.start+l.word.length) b = true := by
        simpa only [ScheduleNode.pivotIndex,ScheduleNode.pivot,hs,rootStep] using hq.2
      have hg := single_pivot_saving_le_maximum φ hP hκ price q.start l.word r.word b hb eligible he
      have hmax : max (paddedRootGain φ P q.reserve q.source-price) 0 ≤
          gapSavingsMaximum φ P q.reserve price q.start q.source.word eligible := by
        rw [hs]
        exact max_le hg (by simpa only [hs] using hR)
      simpa only [hs] using add_le_add hmax (le_refl (gapLogDeficit φ P q.reserve q.source.word))
  · exact add_nonneg hR hDef

private theorem filtered_list_sum_le {α : Type*} (p : α → Bool) (f g : α → ℝ) (qs : List α)
    (hfg : ∀ q ∈ qs, f q ≤ g q) (hg : ∀ q ∈ qs, 0 ≤ g q) :
    ((qs.filter p).map f).sum ≤ (qs.map g).sum := by
  induction qs with
  | nil => exact le_rfl
  | cons q qs ih =>
    have hi := ih (fun x hx => hfg x (List.mem_cons_of_mem q hx)) (fun x hx => hg x (List.mem_cons_of_mem q hx))
    rw [List.filter_cons]
    by_cases hp : p q = true
    · simp only [hp,↓reduceIte,List.map_cons,List.sum_cons]
      exact add_le_add (hfg q (by simp)) hi
    · simp only [hp,↓reduceIte,List.map_cons,List.sum_cons]
      exact hi.trans (le_add_of_nonneg_left (hg q (by simp)))

/-- At every cutoff the visible eligible roots occupy distinct actual
frontier gaps. The sum of their single-pivot savings and positive-sum
deficits is bounded by the actual full-cut observables. -/
theorem visible_gap_budget (φ : ℝ → ℝ) (hφ : Monotone φ) {P κ y : ℝ}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (price : ℝ) (eligible : ℕ → ℝ → Bool) (t : ScheduleTree) (hc : t.Cartesian) :
    ((((parentedNodes 0 κ none t).filter fun q => decide (q.Visible φ (P+Real.exp y))).map
      fun q => visibleNodeScore φ P price eligible q.node).sum) ≤
      totalGapSavingsMaximum φ P κ price eligible (heightCut φ P y t.word)+
        (cutLogProduct (positivePartStep φ) P κ (heightCut φ P y t.word)-
          cutLogProduct φ P κ (heightCut φ P y t.word)) := by
  have hthreshold : φ 0 ≤ P+Real.exp y := by
    have he := Real.exp_pos y
    linarith only [hzero,hP,he]
  have hfront := parentedNodes_visible φ hφ (P+Real.exp y) 0 κ none t hc trivial
  have herase := congrArg (fun qs : List ScheduleNode => (qs.map (visibleNodeScore φ P price eligible)).sum) hfront
  simp only [List.map_map,Function.comp_def] at herase
  rw [herase]
  let F := fun q : ScheduleNode => visibleNodeScore φ P price eligible q
  let G := fun q : ScheduleNode =>
    gapSavingsMaximum φ P q.reserve price q.start q.source.word eligible+gapLogDeficit φ P q.reserve q.source.word
  have hsum := filtered_list_sum_le internalNode F G (indexedFrontier φ (P+Real.exp y) 0 κ t)
    (fun q hq => visibleNodeScore_le_gap φ hP (hzero.trans hP.le) price eligible q (indexedFrontier_reserve_nonnegative hκ hq))
    (fun q hq => add_nonneg (gapSavingsMaximum_nonnegative _ _ _ _ _ _ _)
      (gapLogDeficit_nonnegative φ hP (indexedFrontier_reserve_nonnegative hκ hq) _))
  have hR := indexedFrontier_savings (κ := κ) φ hφ hthreshold price eligible t hc
  have hDef := indexedFrontier_log_deficit (κ := κ) φ hφ hP.le hthreshold t hc
  dsimp only [F,G] at hsum
  rw [List.sum_map_add,hR,hDef] at hsum
  exact hsum

end
end StrongSilver
