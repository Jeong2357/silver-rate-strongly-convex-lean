-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedGoodDepth
import StrongSilver.BandSourceData

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5000000

def bandGoodGainCharge (B μ u : ℝ) : ScheduleNode → ℝ :=
  bandGoodScore B μ u (fun q => |rootGain (cappedStep μ B) q.source|)

def bandEndpointGainEnvelope (κ B μ u : ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  linkedGoodDepthObservable κ B μ u (fourPhaseDepth u) (bandGoodGainCharge B μ u) h y+
  linkedGoodDepthObservable κ B μ u (fourPhaseDepth u+1) (bandGoodGainCharge B μ u) h y

theorem bandGoodGainCharge_nonnegative (B μ u : ℝ) (q : ScheduleNode) : 0 ≤ bandGoodGainCharge B μ u q :=
  bandGoodScore_nonnegative B μ u _ (fun _ => abs_nonneg _) q

theorem bandEndpointGainEnvelope_integrable {κ B μ u a b : ℝ} (h : List ℝ)
    (hB : 1 < B) (hμ : 0 < μ) (hμB : μ*B ≤ 1/2) :
    IntervalIntegrable (bandEndpointGainEnvelope κ B μ u h) volume a b :=
  (linkedGoodDepthObservable_integrable _ _ h hB hμ hμB).add
    (linkedGoodDepthObservable_integrable _ _ h hB hμ hμB)

/-- The exact endpoint-depth gain error has an O(2^d W) source
integral, using the same positioned good vertices and cutoff window. -/
theorem eventually_band_endpoint_gain_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → a ≤ b →
    (∫ y in a..b, bandEndpointGainEnvelope κ B μ u h y) ≤
      C*(2:ℝ)^fourPhaseDepth u*weightedCount h cap := by
  obtain ⟨Ct,hCt,Ht⟩ := eventually_band_linked_good_depth_transport
  obtain ⟨Cg,hCg,Hg⟩ := eventually_band_good_gain_budget
  refine ⟨3*Ct*Cg,by positivity,?_⟩
  filter_upwards [Ht,Hg] with u hTransport hGain
  intro κ B cap μ critical a b h S hab
  let F := bandGoodGainCharge B μ u
  have hBudget := hGain κ B cap μ critical h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa S.threshold_small
    S.scale_upper S.curvature_lower S.curvature_upper S.curvature_half S.noncritical S.critical_charge S.critical_rank
    S.distance_stable S.threshold_count S.rank_lower
  have hd := hTransport κ B μ a b h (fourPhaseDepth u) F (zero_lt_one.trans S.kappa_gt_one).le S.threshold_gt_one
    S.mu_positive S.curvature_half hab (by omega) (bandGoodGainCharge_nonnegative B μ u)
  have hd1 := hTransport κ B μ a b h (fourPhaseDepth u+1) F (zero_lt_one.trans S.kappa_gt_one).le S.threshold_gt_one
    S.mu_positive S.curvature_half hab (by omega) (bandGoodGainCharge_nonnegative B μ u)
  have hScale := mul_le_mul_of_nonneg_left hBudget (show 0 ≤ 3*Ct*(2:ℝ)^fourPhaseDepth u by positivity)
  unfold bandEndpointGainEnvelope
  rw [intervalIntegral.integral_add (linkedGoodDepthObservable_integrable _ _ h S.threshold_gt_one S.mu_positive S.curvature_half)
    (linkedGoodDepthObservable_integrable _ _ h S.threshold_gt_one S.mu_positive S.curvature_half)]
  rw [pow_succ] at hd1
  dsimp only [F,bandGoodGainCharge] at hd hd1 hScale ⊢
  linear_combination hd+hd1+hScale

end
end StrongSilver
