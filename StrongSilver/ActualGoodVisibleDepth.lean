-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodVisibleDepth
import StrongSilver.BandDepthTransport

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6000000

local instance actualDepthVisibleDecidable (G : ScheduleNode → Bool) (H : ScheduleNode → ℝ)
    (parent : Option ScheduleNode) (x : ScheduleNode) (y : ℝ) : Decidable (GoodHeightVisible G H parent x y) := Classical.propDecidable _

/-- The abstract finite tree sum is exactly a sum over actual original
parented occurrences and their positioned descendant subtrees. -/
theorem indexed_goodVisibleDepthTotal (G : ScheduleNode → Bool) (H F : ScheduleNode → ℝ)
    (v y : ℝ) (j start : ℕ) (κ : ℝ) (parent : Option ScheduleNode) (t : ScheduleTree) :
    goodVisibleDepthTotal G H F v j parent (t.indexedTree start κ) y =
      ((parentedNodes start κ parent t).map fun q =>
        if @GoodHeightVisible ScheduleNode G H q.parent q.node y then
          Real.exp (v*y)*goodDepthSum G F j (q.node.source.indexedTree q.node.start q.node.reserve) else 0).sum := by
  classical
  induction t generalizing start κ parent with
  | leaf hw => simp [indexedTree,goodVisibleDepthTotal,parentedNodes]
  | split l b r il ir =>
    simp only [indexedTree,goodVisibleDepthTotal,parentedNodes,List.map_cons,List.map_append,List.sum_cons,List.sum_append,il,ir]
    ring

/-- Height visibility for good labels is precisely visibility at the
actual transformed cutoff. No cutoff-order hypothesis is added. -/
theorem band_good_height_visible_iff (B μ u y : ℝ) (q : ParentedScheduleNode) :
    GoodHeightVisible (bandGoodBool B μ u) (nodePaddedHeight (cappedStep μ B) (bandPad u)) q.parent q.node y ↔
      bandGoodBool B μ u q.node = true ∧ ∃ p, q.parent = some p ∧ bandGoodBool B μ u p = true ∧
        q.Visible (cappedStep μ B) (bandPad u+Real.exp y) := by
  cases hp : q.parent with
  | none => simp [GoodHeightVisible,ParentedScheduleNode.Visible,hp]
  | some p =>
    by_cases hq : bandGoodBool B μ u q.node = true
    · by_cases hg : bandGoodBool B μ u p = true
      · have hqc := ((bandGoodBool_iff B μ u q.node).mp hq).2.1
        have hpc := ((bandGoodBool_iff B μ u p).mp hg).2.1
        simp only [GoodHeightVisible,hp,Option.some.injEq,exists_eq_left',hq,hg,true_and,
          ParentedScheduleNode.Visible,ParentedScheduleNode.parentAbove]
        change (Real.log (cappedStep μ B q.node.pivot-bandPad u) ≤ y ∧
          y < Real.log (cappedStep μ B p.pivot-bandPad u)) ↔ _
        rw [Real.log_le_iff_le_exp (sub_pos.mpr hqc),Real.lt_log_iff_exp_lt (sub_pos.mpr hpc)]
        constructor <;> intro hh <;> constructor <;> linarith only [hh.1,hh.2]
      · simp [GoodHeightVisible,hp,hg]
    · simp [GoodHeightVisible,hp,hq]

/-- Actual visible-root version of (4.24). Any additional restrictions
on the selected gap roots can only reduce this nonnegative sum. -/
theorem eventually_band_actual_depth_transport : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ a b : ℝ, ∀ h : List ℝ, ∀ k : ℕ, ∀ F : ScheduleNode → ℝ,
    0 ≤ κ → 1 < B → μ*B ≤ 1/2 → a ≤ b → k ≤ fourPhaseDepth u+2 → (∀ q, 0 ≤ F q) →
    (∫ y in a..b, ((parentedNodes 0 κ none (cartesian h)).map fun q =>
      if @GoodHeightVisible ScheduleNode (bandGoodBool B μ u) (nodePaddedHeight (cappedStep μ B) (bandPad u)) q.parent q.node y then
        Real.exp (nu*y)*goodDepthSum (bandGoodBool B μ u) F k (q.node.source.indexedTree q.node.start q.node.reserve) else 0).sum) ≤
      C*(2:ℝ)^k*((BinaryForest.labels ((cartesian h).indexedTree 0 κ)).map fun q =>
        Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q)*F q).sum := by
  classical
  obtain ⟨C,hC,H⟩ := eventually_band_depth_transport
  refine ⟨C,hC,?_⟩
  filter_upwards [H,eventually_band_good_edge_deviation] with u hEnvelope hEdges
  intro κ B μ a b h k F hκ hB hμB hab hk hF
  let G := bandGoodBool B μ u
  let HH := nodePaddedHeight (cappedStep μ B) (bandPad u)
  let t := (cartesian h).indexedTree 0 κ
  have he := hEdges κ B μ h hκ hB hμB
  have hp : ∀ p : ScheduleNode, (none : Option ScheduleNode) = some p → G p = true → rootGood G t = true →
      |HH p-rootHeight HH t-Real.log rho| ≤ 11*bandTolerance u := by intro p h; cases h
  have hPoint := goodVisibleDepthTotal_le_envelope G HH F nu (Real.log rho) (11*bandTolerance u) hF k none t he hp
  have hIntegral := intervalIntegral.integral_mono_on hab
    (goodVisibleDepthTotal_integrable G HH F nu a b k none t)
    (goodDepthEnvelope_integrable G HH F nu (Real.log rho+11*bandTolerance u) a b k t)
    (fun y _ => hPoint y)
  have hBound := hEnvelope κ B μ a b h k F hκ hB hμB hab hk hF
  have hRes := hIntegral.trans hBound
  have heq : (fun y => goodVisibleDepthTotal G HH F nu k none t y) = fun y =>
      ((parentedNodes 0 κ none (cartesian h)).map fun q =>
        if @GoodHeightVisible ScheduleNode G HH q.parent q.node y then
          Real.exp (nu*y)*goodDepthSum G F k (q.node.source.indexedTree q.node.start q.node.reserve) else 0).sum := by
    funext y
    exact indexed_goodVisibleDepthTotal G HH F nu y k 0 κ none (cartesian h)
  rw [heq] at hRes
  exact hRes

end
end StrongSilver
