-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.MissingChildIndicator
import StrongSilver.VisibleThroughIntegral
import StrongSilver.ActualGoodVisibleDepth
import StrongSilver.BandMissingGoodChildren

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6800000

local instance bandIncompleteHeightVisibleDecidable (G : ScheduleNode → Bool) (H : ScheduleNode → ℝ)
    (parent : Option ScheduleNode) (x : ScheduleNode) (y : ℝ) : Decidable (GoodHeightVisible G H parent x y) := Classical.propDecidable _

theorem indexed_missing_weight_sum (G : ScheduleNode → Bool) (w : ScheduleNode → ℝ)
    (start : ℕ) (κ : ℝ) (parent : Option ScheduleNode) (t : ScheduleTree) :
    ((BinaryForest.labels (t.indexedTree start κ)).map fun q => w q*missingGoodChildIndicator G q).sum =
      ((parentedNodes start κ parent t).map fun q => missingGoodChildWeight G w q.node).sum := by
  rw [← parentedNodes_erase start κ parent t,List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  exact missingGoodChildIndicator_weight G w q.node

/-- The depth-failure contribution in (4.25). All missing-child costs
come from the actual stable schedule estimate (4.23); the good subtree
is required through depth d+2. -/
theorem eventually_band_incomplete_depth : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → a ≤ b →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    (∫ y in a..b, incompleteVisibleTotal (bandGoodBool B μ u)
      (nodePaddedHeight (cappedStep μ B) (bandPad u)) nu (fourPhaseDepth u+1) none ((cartesian h).indexedTree 0 κ) y) ≤
      C*weightedCount h cap*u^((9:ℝ)/10)*(2:ℝ)^fourPhaseDepth u := by
  classical
  obtain ⟨Ct,hCt,Ht⟩ := eventually_band_actual_depth_transport
  obtain ⟨Cm,hCm,Hm⟩ := eventually_band_missing_good_children
  refine ⟨4*Ct*Cm,by positivity,?_⟩
  filter_upwards [Ht,Hm] with u hTransport hMissing
  intro κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab hcrit hcritical hcriticalRank hD hcount hκW
  let G := bandGoodBool B μ u
  let H := nodePaddedHeight (cappedStep μ B) (bandPad u)
  let M := missingGoodChildIndicator G
  let w := fun q => Real.exp (nu*H q)
  let t := (cartesian h).indexedTree 0 κ
  let S := ((BinaryForest.labels t).map fun q => w q*M q).sum
  have hM : ∀ q, 0 ≤ M q := missingGoodChildIndicator_nonnegative G
  have hS : 0 ≤ S := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (Real.exp_pos _).le (hM q)
  have hCharge : GoodMissingCharge G M t := indexedTree_missing_good_charge G (bandGoodBool_leaf_false B μ u) 0 κ (cartesian h)
  have hPoint := incompleteVisibleTotal_le_through G H M nu hM (fourPhaseDepth u+1) none t hCharge
  have hIntegral := intervalIntegral.integral_mono_on hab
    (incompleteVisibleTotal_integrable G H nu a b (fourPhaseDepth u+1) none t)
    (goodVisibleThroughTotal_integrable G H M nu a b none t ((fourPhaseDepth u+1)+1)) (fun y _ => hPoint y)
  have hEach (k : ℕ) (hk : k < fourPhaseDepth u+2) :
      (∫ y in a..b, goodVisibleDepthTotal G H M nu k none t y) ≤ Ct*(2:ℝ)^k*S := by
    have hk' : k ≤ fourPhaseDepth u+2 := by omega
    have hT := hTransport κ B μ a b h k M (zero_lt_one.trans hκ).le hB hμB hab hk' hM
    have hEq : (fun y => ((parentedNodes 0 κ none (cartesian h)).map fun q =>
        if @GoodHeightVisible ScheduleNode G H q.parent q.node y then
          Real.exp (nu*y)*goodDepthSum G M k (q.node.source.indexedTree q.node.start q.node.reserve) else 0).sum) =
        fun y => goodVisibleDepthTotal G H M nu k none t y := by
      funext y
      exact (indexed_goodVisibleDepthTotal G H M nu y k 0 κ none (cartesian h)).symm
    change (∫ y in a..b, ((parentedNodes 0 κ none (cartesian h)).map fun q =>
      if @GoodHeightVisible ScheduleNode G H q.parent q.node y then
        Real.exp (nu*y)*goodDepthSum G M k (q.node.source.indexedTree q.node.start q.node.reserve) else 0).sum) ≤ Ct*(2:ℝ)^k*S at hT
    rw [hEq] at hT
    exact hT
  have hFinite := goodVisibleThroughTotal_integral_upper G H M nu a b Ct S none t (fourPhaseDepth u+2) hEach
  have hMissingBound := hMissing κ B cap μ critical h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hSM : S ≤ Cm*weightedCount h cap*u^((9:ℝ)/10) := by
    dsimp only [S,M,t]
    rw [indexed_missing_weight_sum G w 0 κ none (cartesian h)]
    exact hMissingBound
  have hDrop : Ct*((2:ℝ)^(fourPhaseDepth u+2)-1)*S ≤ Ct*(2:ℝ)^(fourPhaseDepth u+2)*S := by
    have hh := mul_nonneg hCt.le hS
    nlinarith only [hh]
  have hRank := mul_le_mul_of_nonneg_left hSM
    (mul_nonneg hCt.le (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (fourPhaseDepth u+2)))
  have hFinal := hIntegral.trans (hFinite.trans (hDrop.trans hRank))
  change (∫ y in a..b, incompleteVisibleTotal G H nu (fourPhaseDepth u+1) none t y) ≤ _
  convert hFinal using 1 <;> first | rfl | (simp only [pow_add,pow_two]; ring)

end
end StrongSilver
