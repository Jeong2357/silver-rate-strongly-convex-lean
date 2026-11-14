-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandEndpointGainEnvelope
import StrongSilver.BandPostPairProperties

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 7000000
local instance bandThroughGoodLinkedDecidable (B μ u : ℝ) (q : LinkedGap) : Decidable (GoodLinkedRoot B μ u q) := Classical.propDecidable _

def linkedGoodThroughObservable (κ B μ u : ℝ) (F : ScheduleNode → ℝ) (h : List ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n+1 => fun y => linkedGoodDepthObservable κ B μ u n F h y+linkedGoodThroughObservable κ B μ u F h n y

theorem linkedGoodThroughObservable_integrable {κ B μ u a b : ℝ} (F : ScheduleNode → ℝ) (h : List ℝ)
    (hB : 1 < B) (hμ : 0 < μ) (hμB : μ*B ≤ 1/2) (n : ℕ) :
    IntervalIntegrable (linkedGoodThroughObservable κ B μ u F h n) volume a b := by
  induction n with
  | zero => exact intervalIntegrable_const
  | succ n ih => exact (linkedGoodDepthObservable_integrable n F h hB hμ hμB).add ih

theorem goodThrough_indexed_through_sum (G : ScheduleNode → Bool) (f : ScheduleTree → ℝ)
    (n start : ℕ) (κ : ℝ) (t : ScheduleTree) (hg : GoodThrough G n (t.indexedTree start κ)) :
    goodThroughScore G (fun q => if G q then f q.source else 0) n (t.indexedTree start κ) = throughSum f n t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [goodThroughScore,goodThrough_indexed_level_sum G f n start κ t hg,
      ih (goodThrough_prefix (k:=1) hg),throughSum_succ]
    ring

theorem linkedGoodThroughObservable_frontier (κ B μ u y : ℝ) (F : ScheduleNode → ℝ) (h : List ℝ) (n : ℕ) :
    linkedGoodThroughObservable κ B μ u F h n y =
      ((bandLinkedFrontier κ B μ u y h).map fun q => if GoodLinkedRoot B μ u q then
        Real.exp (nu*y)*goodThroughScore (bandGoodBool B μ u) F n (q.node.source.indexedTree q.node.start q.node.reserve) else 0).sum := by
  classical
  induction n with
  | zero => simp [linkedGoodThroughObservable,goodThroughScore]
  | succ n ih =>
    rw [linkedGoodThroughObservable]
    dsimp only
    rw [ih]
    unfold linkedGoodDepthObservable
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro q hq
    split_ifs
    · change Real.exp (nu*y)*goodDepthSum (bandGoodBool B μ u) F n (q.node.source.indexedTree q.node.start q.node.reserve)+
        Real.exp (nu*y)*goodThroughScore (bandGoodBool B μ u) F n (q.node.source.indexedTree q.node.start q.node.reserve) =
        Real.exp (nu*y)*(goodDepthSum (bandGoodBool B μ u) F n (q.node.source.indexedTree q.node.start q.node.reserve)+
          goodThroughScore (bandGoodBool B μ u) F n (q.node.source.indexedTree q.node.start q.node.reserve))
      ring
    · ring

/-- The sum of all endpoint levels through d+1 still costs only
O(2^d W), by a finite geometric sum of actual depth transports. -/
theorem eventually_band_through_gain_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → a ≤ b →
    (∫ y in a..b, linkedGoodThroughObservable κ B μ u (bandGoodGainCharge B μ u) h (fourPhaseDepth u+2) y) ≤
      C*(2:ℝ)^fourPhaseDepth u*weightedCount h cap := by
  obtain ⟨Ct,hCt,HT⟩ := eventually_band_linked_good_depth_transport
  obtain ⟨Cg,hCg,HG⟩ := eventually_band_good_gain_budget
  refine ⟨4*Ct*Cg,by positivity,?_⟩
  filter_upwards [HT,HG] with u hDepth hGain
  intro κ B cap μ critical a b h S hab
  let F := bandGoodGainCharge B μ u
  let K := Ct*Cg*weightedCount h cap
  have hK : 0 ≤ K := by dsimp only [K]; have hw := weightedCount_nonneg h cap; positivity
  have hGainBound := hGain κ B cap μ critical h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa
    S.threshold_small S.scale_upper S.curvature_lower S.curvature_upper S.curvature_half S.noncritical S.critical_charge
    S.critical_rank S.distance_stable S.threshold_count S.rank_lower
  have hLevel (k : ℕ) (hk : k ≤ fourPhaseDepth u+2) :
      (∫ y in a..b, linkedGoodDepthObservable κ B μ u k F h y) ≤ K*(2:ℝ)^k := by
    have hh := hDepth κ B μ a b h k F (zero_lt_one.trans S.kappa_gt_one).le S.threshold_gt_one S.mu_positive S.curvature_half
      hab hk (bandGoodGainCharge_nonnegative B μ u)
    have hScale := mul_le_mul_of_nonneg_left hGainBound (show 0 ≤ Ct*(2:ℝ)^k by positivity)
    dsimp only [K,F,bandGoodGainCharge] at hh ⊢
    linear_combination hh+hScale
  have hPrefix (n : ℕ) (hn : n ≤ fourPhaseDepth u+3) :
      (∫ y in a..b, linkedGoodThroughObservable κ B μ u F h n y) ≤ K*((2:ℝ)^n-1) := by
    induction n with
    | zero => simp [linkedGoodThroughObservable]
    | succ n ih =>
      have hN := ih (by omega)
      have hD := hLevel n (by omega)
      rw [linkedGoodThroughObservable,intervalIntegral.integral_add
        (linkedGoodDepthObservable_integrable n F h S.threshold_gt_one S.mu_positive S.curvature_half)
        (linkedGoodThroughObservable_integrable F h S.threshold_gt_one S.mu_positive S.curvature_half n),pow_succ]
      linear_combination hN+hD
  have hFinal := hPrefix (fourPhaseDepth u+2) (by omega)
  rw [pow_add] at hFinal
  norm_num at hFinal
  dsimp only [K,F] at hFinal hK ⊢
  linear_combination hFinal+hK

end
end StrongSilver
