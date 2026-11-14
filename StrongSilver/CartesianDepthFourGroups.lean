-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianBalancedScales
import StrongSilver.CartesianGroupAssembly

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3000000

@[simp] theorem depthPhases_map_fst (d : ℕ) (t : ScheduleTree) (b : ℝ) :
    (depthPhases d t b).map Prod.fst = depthFrontier d t := by
  induction d generalizing t b with
  | zero => rfl
  | succ d ih => cases t <;> simp [depthPhases,depthFrontier,ih]

theorem depthPhases_mem_frontier {d : ℕ} {t : ScheduleTree} {b : ℝ} {q : ScheduleTree × ℝ}
    (hq : q ∈ depthPhases d t b) : q.1 ∈ depthFrontier d t := by
  rw [← depthPhases_map_fst d t b]
  exact List.mem_map.mpr ⟨q,hq,rfl⟩

/-- Every actual complete depth frontier lifts to actual four-gap
blocks, retaining the chronological order and every following pivot. -/
theorem exists_depth_four_groups {d : ℕ} {t : ScheduleTree} (b : ℝ)
    (hc : completeThrough (d+2) t) : ∃ qs : List FourGapGroup.Group,
    qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b := by
  have hall (q : ScheduleTree × ℝ) (hq : q ∈ depthPhases d t b) :
      ∃ g : FourGapGroup.Group, (g.1.tree,g.2) = q := by
    obtain ⟨G,hG⟩ := depth_group_decomposition hc (depthPhases_mem_frontier hq)
    exact ⟨(G,q.2),by rw [hG]⟩
  generalize hs : depthPhases d t b = ps at hall ⊢
  clear hs
  induction ps with
  | nil => exact ⟨[],rfl⟩
  | cons q ps ih =>
    obtain ⟨g,hg⟩ := hall q (by simp)
    obtain ⟨gs,hgs⟩ := ih (fun p hp => hall p (List.mem_cons_of_mem q hp))
    exact ⟨g::gs,by simp only [List.map_cons,hg,hgs]⟩

namespace FourGapGroup

theorem depth_groups_word {d : ℕ} {t : ScheduleTree} {b : ℝ} {qs : List Group}
    (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b) :
    qs.flatMap groupWord = t.word++[b] := by
  change qs.flatMap (fun q => q.1.tree.word++[q.2]) = t.word++[b]
  have hh := congrArg (fun ps : List (ScheduleTree × ℝ) => ps.flatMap (fun q => q.1.word++[q.2])) hqs
  simpa only [List.flatMap_map,Function.comp_def,groupWord,depthPhases_word] using hh

theorem depth_groups_count {d : ℕ} {t : ScheduleTree} {b : ℝ} {qs : List Group}
    (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b) : qs.length ≤ 2^d := by
  have hh := congrArg List.length hqs
  rw [List.length_map,depthPhases_length] at hh
  rw [hh]
  exact depthFrontier_length_le d t

theorem tree_drawdown_eq_last {G : FourGapGroup} {φ : ℝ → ℝ}
    (hKM : 0 < adjustedExcess φ G.left G.middlePivot)
    (hKR : 0 < adjustedExcess φ G.third G.rightPivot) :
    G.tree.gapDrawdown φ = G.fourth.gapDrawdown φ :=
  (positive_excess_mass_identity φ G.left G.right G.middlePivot hKM).2.trans
    (positive_excess_mass_identity φ G.third G.fourth G.rightPivot hKR).2

end FourGapGroup

theorem frontier_sum_eq_levelSum (f : ScheduleTree → ℝ) (hf : ∀ h, f (.leaf h) = 0)
    (d : ℕ) (t : ScheduleTree) : ((depthFrontier d t).map f).sum = levelSum f d t := by
  induction d generalizing t with
  | zero => cases t <;> simp [depthFrontier,levelSum,hf]
  | succ d ih => cases t <;> simp [depthFrontier,levelSum,hf,ih]

namespace FourGapGroup

theorem depth_groups_gain_sum {d : ℕ} {t : ScheduleTree} {b : ℝ} {qs : List Group}
    (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b) (φ : ℝ → ℝ) :
    (qs.map fun q => FourPhase.signedThreeGain (rootGain φ q.1.tree) (rootGain φ q.1.left) (rootGain φ q.1.right)).sum =
      levelSum (fourGain φ) d t := by
  have hm := congrArg (List.map Prod.fst) hqs
  simp only [List.map_map,depthPhases_map_fst,Function.comp_def] at hm
  have hh := congrArg (fun ts : List ScheduleTree => (ts.map (fourGain φ)).sum) hm
  rw [frontier_sum_eq_levelSum (fourGain φ) (fun h => by simp [fourGain,rootGain,levelSum])] at hh
  simpa only [List.map_map,Function.comp_def,fourGain,levelSum,tree,left,right,FourPhase.signedThreeGain,add_assoc] using hh

end FourGapGroup
end
end StrongSilver.ScheduleTree
