-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FrontierHeightWindowSum
import StrongSilver.BandFullKernelEnvelope

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 8500000

def bandOriginalWindowScore (B μ u y : ℝ) (k : ℕ) (b : ScheduleNode) : ℝ :=
  if bandPad u < cappedStep μ B b.pivot ∧ y-(k:ℝ)*Real.log rho < nodePaddedHeight (cappedStep μ B) (bandPad u) b ∧
      nodePaddedHeight (cappedStep μ B) (bandPad u) b ≤ y
  then normalizedNodeDecrease (cappedStep μ B) (bandPad u) b else 0

theorem band_frontier_window_sum {κ B μ u y : ℝ} (h : List ℝ) (k : ℕ) (hμ : 0 < μ) (hμB : μ*B ≤ 1/2) :
    ((bandIndexedFrontier κ B μ u y h).map (bandGapWindowPower B μ u y k)).sum =
      ((labels ((cartesian h).indexedTree 0 κ)).map (bandOriginalWindowScore B μ u y k)).sum := by
  let φ := cappedStep μ B
  let P := bandPad u
  have hφ := cappedStep_monotone (B:=B) hμ (by linarith only [hμB])
  have hh := frontier_height_window_sum φ hφ P (y-(k:ℝ)*Real.log rho) (P+Real.exp y) 0 κ (cartesian h) (cartesian_valid h)
    (normalizedNodeDecrease φ P)
  change _ = _ at hh
  refine hh.trans ?_
  congr 1
  apply List.map_congr_left
  intro b hb
  have hIff : (φ b.pivot ≤ P+Real.exp y ∧ P < φ b.pivot ∧ y-(k:ℝ)*Real.log rho < nodePaddedHeight φ P b) ↔
      (P < φ b.pivot ∧ y-(k:ℝ)*Real.log rho < nodePaddedHeight φ P b ∧ nodePaddedHeight φ P b ≤ y) := by
    constructor
    · intro hs
      refine ⟨hs.2.1,hs.2.2,?_⟩
      apply (Real.log_le_iff_le_exp (sub_pos.mpr hs.2.1)).mpr
      linarith only [hs.1]
    · intro hs
      have hh := (Real.log_le_iff_le_exp (sub_pos.mpr hs.1)).mp hs.2.2
      exact ⟨by linarith only [hh],hs.1,hs.2.1⟩
  dsimp only [bandOriginalWindowScore,φ,P] at hIff ⊢
  simp only [hIff]

theorem bandOriginalWindowScore_indicator (B μ u y : ℝ) (k : ℕ) (b : ScheduleNode) :
    bandOriginalWindowScore B μ u y k b =
      if bandPad u < cappedStep μ B b.pivot then
        depthWindowIndicator k (y-nodePaddedHeight (cappedStep μ B) (bandPad u) b)*
          normalizedNodeDecrease (cappedStep μ B) (bandPad u) b else 0 := by
  let H := nodePaddedHeight (cappedStep μ B) (bandPad u) b
  by_cases hp : bandPad u < cappedStep μ B b.pivot
  · rw [if_pos hp]
    by_cases hw : 0 ≤ y-H ∧ y-H < (k:ℝ)*Real.log rho
    · have hc : bandPad u < cappedStep μ B b.pivot ∧ y-(k:ℝ)*Real.log rho < H ∧ H ≤ y := by
        exact ⟨hp,by linarith only [hw.2],by linarith only [hw.1]⟩
      dsimp only [H] at hw hc
      simp only [bandOriginalWindowScore,if_pos hc,depthWindowIndicator,if_pos hw,one_mul]
    · have hc : ¬ (bandPad u < cappedStep μ B b.pivot ∧ y-(k:ℝ)*Real.log rho < H ∧ H ≤ y) := by
        intro hh
        apply hw
        exact ⟨by linarith only [hh.2.2],by linarith only [hh.2.1]⟩
      dsimp only [H] at hw hc
      simp only [bandOriginalWindowScore,if_neg hc,depthWindowIndicator,if_neg hw,zero_mul]
  · simp only [bandOriginalWindowScore,hp,false_and,if_neg hp,↓reduceIte]

/-- At each inner-band cutoff, all three original height windows lie
inside the protected source band. -/
theorem eventually_band_frontier_protected_window : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y : ℝ, ∀ h : List ℝ, ∀ k : ℕ,
    0 < μ → μ*B ≤ 1/2 → y ∈ Icc (innerBandLow u) (innerBandHigh u) → k ≤ fourPhaseDepth u+2 →
    ((bandIndexedFrontier κ B μ u y h).map (bandGapWindowPower B μ u y k)).sum =
      ((bandProtectedNodes κ B μ u h).map fun q => bandOriginalWindowScore B μ u y k q.node).sum := by
  filter_upwards [eventually_inner_band_kernel_window] with u H
  intro κ B μ y h k hμ hμB hy hk
  have hWindow := H y k hy hk
  have hProtected (b : ScheduleNode) (hb : bandPad u < cappedStep μ B b.pivot ∧
      y-(k:ℝ)*Real.log rho < nodePaddedHeight (cappedStep μ B) (bandPad u) b ∧
      nodePaddedHeight (cappedStep μ B) (bandPad u) b ≤ y) : bandProtectedPredicate B μ u b :=
    ⟨hb.1,hWindow.2.1.1.trans_lt hb.2.1,by linarith only [hb.2.2,hWindow.2.2]⟩
  rw [band_frontier_window_sum h k hμ hμB,← parentedNodes_erase]
  simp only [List.map_map,Function.comp_def]
  rw [bandProtectedNodes_eq,list_filter_prop_sum_eq]
  congr 1
  apply List.map_congr_left
  intro q hq
  by_cases hp : bandProtectedPredicate B μ u q.node
  · rw [if_pos hp]
  · rw [if_neg hp]
    unfold bandOriginalWindowScore
    apply if_neg
    intro hh
    exact hp (hProtected q.node hh)

/-- Exact finite kernel representation on the same original protected
occurrence list used by the absolute power-jump budget. -/
theorem eventually_band_kernel_representation : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y : ℝ, ∀ h : List ℝ,
    0 < μ → μ*B ≤ 1/2 → y ∈ Icc (innerBandLow u) (innerBandHigh u) →
    ((bandIndexedFrontier κ B μ u y h).map (bandKernelGapPower B μ u y)).sum =
      ((bandProtectedNodes κ B μ u h).map fun q =>
        silverAveragingKernel (fourPhaseDepth u) (y-nodePaddedHeight (cappedStep μ B) (bandPad u) q.node)*
          normalizedNodeDecrease (cappedStep μ B) (bandPad u) q.node).sum := by
  classical
  filter_upwards [eventually_band_frontier_protected_window] with u H
  intro κ B μ y h hμ hμB hy
  unfold bandKernelGapPower
  rw [List.sum_map_add,List.sum_map_add,List.sum_map_mul_left,List.sum_map_mul_left,
    H κ B μ y h (fourPhaseDepth u) hμ hμB hy (by omega),
    H κ B μ y h (fourPhaseDepth u+1) hμ hμB hy (by omega),
    H κ B μ y h (fourPhaseDepth u+2) hμ hμB hy (by omega),
    ← List.sum_map_mul_left,← List.sum_map_mul_left,← List.sum_map_add,← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro q hq
  have hPred := (List.mem_filter.mp ((bandProtectedNodes_eq κ B μ u h) ▸ hq)).2
  have hP : bandPad u < cappedStep μ B q.node.pivot := (of_decide_eq_true hPred).1
  rw [bandOriginalWindowScore_indicator,bandOriginalWindowScore_indicator,bandOriginalWindowScore_indicator,
    if_pos hP,if_pos hP,if_pos hP]
  unfold silverAveragingKernel
  ring

end
end StrongSilver
