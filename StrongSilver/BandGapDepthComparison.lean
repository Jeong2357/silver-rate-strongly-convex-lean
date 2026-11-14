-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.DepthHeightDisagreement
import StrongSilver.IndexedActiveRootOrder
import StrongSilver.BandPairErrorPointwise
import StrongSilver.BandExcludedForest

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 8200000

namespace BinaryForest

theorem goodThrough_mono {α : Type*} {G : α → Bool} {k n : ℕ} {t : BinaryTree α}
    (hkn : k ≤ n) (h : GoodThrough G n t) : GoodThrough G k t := by
  have he : k+(n-k) = n := Nat.add_sub_of_le hkn
  apply goodThrough_prefix (k:=n-k)
  rwa [he]

theorem activeRootOrder_height_le {α : Type*} {active : α → Prop} {H : α → ℝ} {t : BinaryTree α}
    (ho : ActiveRootOrder active H t) {b : α} (hb : b ∈ labels t) (ha : active b) : H b ≤ rootHeight H t := by
  cases t with
  | nil => simp [labels] at hb
  | node v l r => exact ho.1 b hb ha

end BinaryForest

theorem indexedTree_internal_root_height {q : ScheduleNode} (H : ScheduleNode → ℝ) (hq : internalNode q = true) :
    rootHeight H (q.source.indexedTree q.start q.reserve) = H q := by
  cases hs : q.source with
  | leaf word => simp [internalNode,hs] at hq
  | split l b r =>
    simp only [hs,indexedTree,rootHeight]
    congr
    exact hs.symm

def bandGapPrefixPower (B μ u : ℝ) (k : ℕ) (q : ScheduleNode) : ℝ :=
  ((depthPrefixLabels k (q.source.indexedTree q.start q.reserve)).map (normalizedNodeDecrease (cappedStep μ B) (bandPad u))).sum

def bandDepthBoundaryCost (B μ u y : ℝ) (k : ℕ) (q : ScheduleNode) : ℝ := by
  classical
  exact ((labels (q.source.indexedTree q.start q.reserve)).map fun b =>
    if bandPad u < cappedStep μ B b.pivot ∧
      |y-nodePaddedHeight (cappedStep μ B) (bandPad u) b-(k:ℝ)*Real.log rho| ≤ (k:ℝ)*(11*bandTolerance u)
    then |normalizedNodeDecrease (cappedStep μ B) (bandPad u) b| else 0).sum

/-- For an actual available pair, replacing any of the three kernel
height windows by its complete good depth prefix has only the stated
boundary-strip error, including all original signed descendants. -/
theorem eventually_band_gap_depth_comparison : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical y : ℝ, ∀ h : List ℝ, ∀ R : List CutPhase,
    BandSourceData κ B cap μ critical u h → ∀ q r : LinkedGap,
    (q,r) ∈ bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h R y →
    ∀ k : ℕ, k ≤ fourPhaseDepth u+2 →
    bandGapWindowPower B μ u y k q.node ≤ bandGapPrefixPower B μ u k q.node+bandDepthBoundaryCost B μ u y k q.node := by
  classical
  filter_upwards [eventually_band_forest_spacing,eventually_band_candidate_height] with u hTol hHeight
  intro κ B cap μ critical y h R S q r hPair k hk
  let φ := cappedStep μ B
  let P := bandPad u
  let G := bandGoodBool B μ u
  let H := nodePaddedHeight φ P
  let t := q.node.source.indexedTree q.node.start q.node.reserve
  let F := normalizedNodeDecrease φ P
  let active := fun b : ScheduleNode => P < φ b.pivot
  have hPre := bandPostReservedPairs_pre hPair
  have hSub := bandPostReservedPairs_adjacent_sublist κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h R y
  have hq := (adjacentOccurrences_members (hSub.subset hPair)).1
  have hInt := bandGoodBool_internal hPre.1.1.1
  have hMem := linkedFrontier_internal_mem hq hInt
  have hCart := indexedTree_source_cartesian (cartesian_valid h) hMem
  have hReserve := indexedTree_reserve_nonnegative (zero_lt_one.trans S.kappa_gt_one).le hMem
  have hφ := cappedStep_monotone (B:=B) S.mu_positive (by linarith only [S.curvature_half])
  have hZero : φ 0 ≤ 0 := by simp only [φ,cappedStep,if_pos (zero_lt_one.trans S.threshold_gt_one).le,logarithmicStep_zero,le_refl]
  have hEdges := indexedTree_good_edge_deviation G φ (Real.exp_pos _) hReserve hZero hTol.1 hTol.2.1
    (fun b hb => paddedGood_balanced ((bandGoodBool_iff B μ u b).mp hb).1) q.node.start q.node.source
  have hOrder := indexedTree_active_root_order φ hφ P q.node.start q.node.reserve q.node.source hCart
  have hGood : GoodThrough G (k+1) t := goodThrough_mono (by omega) hPre.2.2
  have hHeights := hHeight κ B μ y h q (zero_lt_one.trans S.kappa_gt_one).le S.threshold_gt_one S.curvature_half hq hPre.1.1
  have hRoot : rootHeight H t = H q.node := indexedTree_internal_root_height H hInt
  have hLo : rootHeight H t ≤ y := by rw [hRoot]; linarith only [hHeights.1]
  have hHi : y-rootHeight H t ≤ Real.log rho+11*bandTolerance u := by rw [hRoot]; exact hHeights.2
  have hActive : ∀ b, G b = true → active b := fun b hb => ((bandGoodBool_iff B μ u b).mp hb).2.1
  have hActual := depth_height_window_upper G H F active (Real.log rho) (11*bandTolerance u) y k t
    log_rho_positive.le (mul_nonneg (by norm_num) hTol.1) hGood hEdges hOrder hActive hLo hHi
  have hUpper (b : ScheduleNode) (hb : b ∈ labels t) (ha : active b) : H b ≤ y :=
    (activeRootOrder_height_le hOrder hb ha).trans hLo
  have hWindow : bandGapWindowPower B μ u y k q.node =
      ((labels t).map fun b => if active b ∧ y-(k:ℝ)*Real.log rho < H b ∧ H b ≤ y then F b else 0).sum := by
    unfold bandGapWindowPower
    rw [indexed_height_window_labels φ hφ P _ _ _ _ hCart,list_filter_sum_eq]
    congr 1
    apply List.map_congr_left
    intro b hb
    by_cases hc : active b ∧ y-(k:ℝ)*Real.log rho < H b
    · have ht := hUpper b hb hc.1
      have hct : active b ∧ y-(k:ℝ)*Real.log rho < H b ∧ H b ≤ y := ⟨hc.1,hc.2,ht⟩
      rw [if_pos hct]
      split_ifs with hflag
      · rfl
      · have hn : ¬ (P < φ b.pivot ∧ y-(k:ℝ)*Real.log rho < nodePaddedHeight φ P b) :=
          of_decide_eq_false (Bool.eq_false_iff.mpr hflag)
        exact False.elim (hn hc)
    · have hct : ¬ (active b ∧ y-(k:ℝ)*Real.log rho < H b ∧ H b ≤ y) := fun hh => hc ⟨hh.1,hh.2.1⟩
      rw [if_neg hct]
      split_ifs with hflag
      · exact False.elim (hc (of_decide_eq_true hflag))
      · rfl
  rw [hWindow]
  exact hActual

end
end StrongSilver
