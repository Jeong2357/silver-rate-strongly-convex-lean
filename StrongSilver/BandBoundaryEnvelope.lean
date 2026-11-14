-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandBoundaryWindow
import StrongSilver.BandSourceData
import StrongSilver.BandAbsoluteGainBudget
import StrongSilver.FiniteListIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6500000

def bandBoundaryEnvelope (κ B μ u : ℝ) (k : ℕ) (h : List ℝ) (y : ℝ) : ℝ :=
  ((bandProtectedNodes κ B μ u h).map fun q =>
    |normalizedNodeDecrease (cappedStep μ B) (bandPad u) q.node| *
      bandBoundaryWindow u (nodePaddedHeight (cappedStep μ B) (bandPad u) q.node) k y).sum

theorem bandBoundaryEnvelope_integrable (κ B μ u a b : ℝ) (k : ℕ) (h : List ℝ) :
    IntervalIntegrable (bandBoundaryEnvelope κ B μ u k h) volume a b :=
  intervalIntegrable_list_sum _ _ a b (fun q _ => (bandBoundaryWindow_integrable u _ a b k).const_mul _)

theorem normalizedNodeDecrease_abs_weight (φ : ℝ → ℝ) (P : ℝ) (q : ScheduleNode) :
    |normalizedNodeDecrease φ P q| *Real.exp (nu*nodePaddedHeight φ P q) = |paddedRootDecrease φ P q.reserve q.source| := by
  unfold normalizedNodeDecrease
  rw [abs_div,abs_of_pos (Real.exp_pos _)]
  exact div_mul_cancel₀ _ (Real.exp_ne_zero _)

/-- All original boundary-strip errors have one source O(W) budget.
The exponential window contributes 2^k*k*delta and every power jump is
charged at its original positioned occurrence only. -/
theorem eventually_band_boundary_envelope_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ, ∀ k : ℕ,
    BandSourceData κ B cap μ critical u h → a ≤ b → k ≤ fourPhaseDepth u+2 →
    (∫ y in a..b, bandBoundaryEnvelope κ B μ u k h y) ≤
      C*(2:ℝ)^k*(k:ℝ)*bandTolerance u*weightedCount h cap := by
  obtain ⟨Cw,hCw,HW⟩ := eventually_band_boundary_window_integral
  obtain ⟨Ca,hCa,HA⟩ := eventually_band_absolute_gain_budget
  refine ⟨Cw*Ca,mul_pos hCw hCa,?_⟩
  filter_upwards [HW,HA,eventually_gt_atTop (0:ℝ)] with u hWindow hAbs hu
  intro κ B cap μ critical a b h k S hab hk
  let φ := cappedStep μ B
  let P := bandPad u
  let qs := bandProtectedNodes κ B μ u h
  let K := Cw*(2:ℝ)^k*(k:ℝ)*bandTolerance u
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hPoint : ∀ q ∈ qs,
      (∫ y in a..b, |normalizedNodeDecrease φ P q.node| *bandBoundaryWindow u (nodePaddedHeight φ P q.node) k y) ≤
      K*|paddedRootDecrease φ P q.node.reserve q.node.source| := by
    intro q hq
    rw [intervalIntegral.integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left (hWindow (nodePaddedHeight φ P q.node) a b k hab hk)
      (abs_nonneg (normalizedNodeDecrease φ P q.node))
    calc
      _ ≤ |normalizedNodeDecrease φ P q.node| *(K*Real.exp (nu*nodePaddedHeight φ P q.node)) := hh
      _ = K*|paddedRootDecrease φ P q.node.reserve q.node.source| := by
        rw [show |normalizedNodeDecrease φ P q.node| *(K*Real.exp (nu*nodePaddedHeight φ P q.node)) =
          K*(|normalizedNodeDecrease φ P q.node| *Real.exp (nu*nodePaddedHeight φ P q.node)) by ring,normalizedNodeDecrease_abs_weight]
  have hSum := List.sum_le_sum hPoint
  rw [List.sum_map_mul_left] at hSum
  have hAbsBound := hAbs κ B cap μ critical h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa S.scale_upper
    S.curvature_lower S.curvature_upper S.curvature_half S.noncritical S.critical_charge S.critical_rank S.distance_stable S.threshold_count S.rank_lower
  have hGainNonneg : 0 ≤ ((bandProtectedNodes κ B μ u h).map fun q =>
      Real.exp (nu*parentedHeight φ P q)*|paddedRootGain φ P q.node.reserve q.node.source|).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hPower : (qs.map fun q => |paddedRootDecrease φ P q.node.reserve q.node.source|).sum ≤ Ca*weightedCount h cap := by
    dsimp only [qs,φ,P]
    linarith only [hAbsBound,hGainNonneg]
  have hScaled := mul_le_mul_of_nonneg_left hPower hK
  unfold bandBoundaryEnvelope
  rw [integral_list_sum _ _ a b (fun q _ => (bandBoundaryWindow_integrable u _ a b k).const_mul _)]
  dsimp only [qs,φ,P,K] at hSum hScaled ⊢
  linear_combination hSum+hScaled

end
end StrongSilver
