-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodDepthSpacing
import StrongSilver.BandGoodChildGeometry

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter
noncomputable section
set_option maxHeartbeats 5400000

/-- Both-sided spacing holds on the original indexed tree for any
choice of good labels that implies the actual padded balance property. -/
theorem indexedTree_good_edge_deviation (G : ScheduleNode → Bool) (φ : ℝ → ℝ) {P δ κ : ℝ}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100)
    (hG : ∀ q, G q = true → PaddedBalanced φ P q.reserve δ q.source)
    (start : ℕ) (t : ScheduleTree) :
    GoodEdgeDeviation G (nodePaddedHeight φ P) (Real.log rho) (11*δ) (indexedTree start κ t) := by
  induction t generalizing start κ with
  | leaf hw => trivial
  | split l b r il ir =>
    refine ⟨il (le_refl (0:ℝ)) start,ir hκ (start+l.word.length+1),?_,?_⟩
    · intro hp hc
      have hparent := hG ⟨start,.split l b r,κ⟩ hp
      cases l with
      | leaf hw => simp [indexedTree,rootGood] at hc
      | split ll lb lr =>
        have hchild := hG ⟨start,.split ll lb lr,0⟩ hc
        exact padded_balanced_left_spacing hP hκ hzero hδ hδmax hparent hchild
    · intro hp hc
      have hparent := hG ⟨start,.split l b r,κ⟩ hp
      cases r with
      | leaf hw => simp [indexedTree,rootGood] at hc
      | split rl rb rr =>
        have hchild := hG ⟨start+l.word.length+1,.split rl rb rr,κ⟩ hc
        exact padded_balanced_right_spacing hP hκ hzero hδ hδmax hparent hchild

theorem eventually_band_good_edge_deviation : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ : ℝ, ∀ h : List ℝ, 0 ≤ κ → 1 < B → μ*B ≤ 1/2 →
    GoodEdgeDeviation (bandGoodBool B μ u) (nodePaddedHeight (cappedStep μ B) (bandPad u))
      (Real.log rho) (11*bandTolerance u) ((cartesian h).indexedTree 0 κ) := by
  filter_upwards [eventually_band_forest_spacing] with u H
  intro κ B μ h hκ hB hμB
  apply indexedTree_good_edge_deviation (bandGoodBool B μ u) (cappedStep μ B) (Real.exp_pos _) hκ
    (by simp only [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero,le_refl]) H.1 H.2.1
  intro q hq
  exact paddedGood_balanced ((bandGoodBool_iff B μ u q).mp hq).1

end
end StrongSilver
