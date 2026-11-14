-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianCappedGain
import StrongSilver.CartesianDepthLogFactors
import StrongSilver.CartesianGroupLogRateFactors

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3600000

theorem frontier_word_sublist {d : ℕ} {t s : ScheduleTree} (h : s ∈ depthFrontier d t) : s.word.Sublist t.word := by
  induction d generalizing t with
  | zero => simp only [depthFrontier,List.mem_singleton] at h; subst s; rfl
  | succ d ih =>
    cases t with
    | leaf hw => simp only [depthFrontier,List.mem_singleton] at h; subst s; rfl
    | split l b r =>
      simp only [depthFrontier,List.mem_append] at h
      exact h.elim (fun h => (ih h).trans (left_word_sublist l r b))
        (fun h => (ih h).trans (right_word_sublist l r b))

theorem positiveExcessThrough_prefix {φ : ℝ → ℝ} {d k : ℕ} {t : ScheduleTree}
    (h : positiveExcessThrough φ (d+k) t) : positiveExcessThrough φ d t := by
  induction d generalizing t with
  | zero => trivial
  | succ d ih =>
    rw [Nat.succ_add] at h
    cases t with
    | leaf hw => trivial
    | split l b r => exact ⟨h.1,ih h.2.1,ih h.2.2⟩

theorem positiveExcessThrough_frontier {φ : ℝ → ℝ} {d k : ℕ} {t s : ScheduleTree}
    (h : positiveExcessThrough φ (d+k) t) (hs : s ∈ depthFrontier d t) : positiveExcessThrough φ k s := by
  induction d generalizing t with
  | zero =>
    simp only [depthFrontier,List.mem_singleton] at hs
    subst s
    simpa only [Nat.zero_add] using h
  | succ d ih =>
    rw [Nat.succ_add] at h
    cases t with
    | leaf hw =>
      simp only [depthFrontier,List.mem_singleton] at hs
      subst s
      cases k <;> trivial
    | split l b r =>
      simp only [depthFrontier,List.mem_append] at hs
      exact hs.elim (fun hs => ih h.2.1 hs) (fun hs => ih h.2.2 hs)

namespace FourGapGroup

/-- Exact logarithmic rate of the fully constructed depth extension:
the coefficient-weighted signed gain S_d, the exterior factor, and the
explicit sum of finite losses. Both transform branches are respected. -/
theorem depth_sequence_log_rate {C μ B ε η Z : ℝ} {d : ℕ} {t : ScheduleTree} {b : ℝ} {qs : List Group}
    (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b)
    (hword : ∀ s ∈ t.word, s ≤ B)
    (hpos : positiveExcessThrough (cappedStep μ B) (d+2) t)
    (hterm : 0 < terminalFactor (cappedStep μ B) t b) :
    0 < sequenceRate C μ B ε η qs Z ∧
    Real.log (sequenceRate C μ B ε η qs Z) =
      2*Real.log (terminalFactor (cappedStep μ B) t b)+silverDepthGain (cappedStep μ B) d t-
        C*sequenceLoss μ ε η qs Z := by
  have hposd := positiveExcessThrough_prefix (k := 2) hpos
  have hleading (q : Group) (hq : q ∈ qs) :
      q.1.leadingFactor μ B q.2 = terminalFactor (cappedStep μ B) q.1.tree q.2 := by
    have hphase : (q.1.tree,q.2) ∈ depthPhases d t b := hqs ▸ List.mem_map.mpr ⟨q,hq,rfl⟩
    have hfront := depthPhases_mem_frontier hphase
    have hlocal := positiveExcessThrough_frontier hpos hfront
    have hsub := frontier_word_sublist hfront
    exact leadingFactor_eq_terminalFactor (fun s hs => hword s (hsub.subset hs)) hlocal.1 hlocal.2.2.1
  have hleadpos (q : Group) (hq : q ∈ qs) : 0 < q.1.leadingFactor μ B q.2 := by
    rw [hleading q hq]
    have hphase : (q.1.tree,q.2) ∈ depthPhases d t b := hqs ▸ List.mem_map.mpr ⟨q,hq,rfl⟩
    exact depthPhases_terminal_positive (cappedStep μ B) hposd hterm _ hphase
  have hlogs : (qs.map fun q => Real.log (q.1.leadingFactor μ B q.2)).sum =
      Real.log (terminalFactor (cappedStep μ B) t b)+throughSum (rootGain (cappedStep μ B)) d t := by
    have hm : qs.map (fun q => Real.log (q.1.leadingFactor μ B q.2)) =
        qs.map (fun q => Real.log (terminalFactor (cappedStep μ B) q.1.tree q.2)) :=
      List.map_congr_left (fun q hq => congrArg Real.log (hleading q hq))
    rw [hm]
    have hh := congrArg (fun ps : List (ScheduleTree × ℝ) =>
      (ps.map fun q => Real.log (terminalFactor (cappedStep μ B) q.1 q.2)).sum) hqs
    simp only [List.map_map,Function.comp_def] at hh
    exact hh.trans (depthPhases_log_factor_sum (cappedStep μ B) hposd hterm)
  have hfour : levelSum (fourGain (cappedStep μ B)) d t = levelSum (fourGain (logarithmicStep μ)) d t := by
    rw [fourGain_level_identity,fourGain_level_identity,
      levelSum_rootGain_capped d t hword,levelSum_rootGain_capped (d+1) t hword]
  have hgain := (depth_groups_gain_sum hqs (logarithmicStep μ)).trans hfour.symm
  refine ⟨sequenceRate_positive_of_factors hleadpos,?_⟩
  rw [log_sequenceRate_of_factors hleadpos,hgain,hlogs,silverDepthGain]
  ring

end FourGapGroup
end
end StrongSilver.ScheduleTree
