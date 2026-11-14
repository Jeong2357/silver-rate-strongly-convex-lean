-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandKernelRepresentation
import StrongSilver.BandKernelWeight
import StrongSilver.SilverKernelConvolution
import StrongSilver.BandAbsoluteGainBudget
import StrongSilver.FiniteListIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 11000000

def bandWeightedPowerJumps (κ B μ u : ℝ) (h : List ℝ) : ℝ :=
  ((bandProtectedNodes κ B μ u h).map fun q =>
    smoothedBandWeight u (u/bandRatio) (Real.log q.node.pivot)*
      paddedRootDecrease (cappedStep μ B) (bandPad u) q.node.reserve q.node.source).sum

def bandKernelConvolution (κ B μ u : ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  bandHeightWeight μ u y*Real.exp (nu*y)*((bandProtectedNodes κ B μ u h).map fun q =>
    silverAveragingKernel (fourPhaseDepth u) (y-nodePaddedHeight (cappedStep μ B) (bandPad u) q.node)*
      normalizedNodeDecrease (cappedStep μ B) (bandPad u) q.node).sum

/-- Exact finite expansion of the convolution into original jump
integrals, with each original exponential weight retained. -/
theorem bandKernelConvolution_integral {κ B μ u a b : ℝ} (h : List ℝ) (hμ : 0 < μ) :
    IntervalIntegrable (bandKernelConvolution κ B μ u h) volume a b ∧
    (∫ y in a..b, bandKernelConvolution κ B μ u h y) =
      ((bandProtectedNodes κ B μ u h).map fun q =>
        (paddedRootDecrease (cappedStep μ B) (bandPad u) q.node.reserve q.node.source/
          Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q.node))*
        (∫ y in a..b, bandHeightWeight μ u y*(silverAveragingKernel (fourPhaseDepth u)
          (y-nodePaddedHeight (cappedStep μ B) (bandPad u) q.node)*Real.exp (nu*y)))).sum := by
  let φ := cappedStep μ B
  let P := bandPad u
  let d := fourPhaseDepth u
  let qs := bandProtectedNodes κ B μ u h
  let F := fun q : ParentedScheduleNode => fun y => (paddedRootDecrease φ P q.node.reserve q.node.source/
    Real.exp (nu*nodePaddedHeight φ P q.node))*(bandHeightWeight μ u y*
      (silverAveragingKernel d (y-nodePaddedHeight φ P q.node)*Real.exp (nu*y)))
  have hInt (q : ParentedScheduleNode) : IntervalIntegrable (F q) volume a b :=
    ((silverAveragingKernel_integrable d (nodePaddedHeight φ P q.node) nu a b).continuousOn_mul
      (bandHeightWeight_continuous hμ).continuousOn).const_mul _
  have hEq : bandKernelConvolution κ B μ u h = fun y => (qs.map fun q => F q y).sum := by
    funext y
    unfold bandKernelConvolution
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro q hq
    dsimp only [F,φ,P,d,normalizedNodeDecrease]
    ring
  rw [hEq]
  refine ⟨intervalIntegrable_list_sum F qs a b (fun q _ => hInt q),?_⟩
  rw [integral_list_sum F qs a b (fun q _ => hInt q)]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact intervalIntegral.integral_const_mul _ _

/-- The exact averaged original jump sum at offset P differs from its
height-kernel convolution by a fixed negative power times W. -/
theorem eventually_band_kernel_approximation : ∃ K > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h →
    |bandWeightedPowerJumps κ B μ u h-
      (∫ y in innerBandLow u..innerBandHigh u, bandKernelConvolution κ B μ u h y)/silverKernelMass (fourPhaseDepth u)| ≤
      K*weightedCount h cap*u^(-(1:ℝ)/1000) := by
  classical
  obtain ⟨Ca,hCa,HA⟩ := eventually_band_absolute_gain_budget
  refine ⟨Ca,hCa,?_⟩
  filter_upwards [HA,eventually_band_kernel_weight_difference,eventually_band_weighted_kernel_support,
    eventually_kernel_weight_error_rate,eventually_inner_band_geometry] with u hAbsolute hDifference hSupport hRate hGeometry
  intro κ B cap μ critical h S
  let φ := cappedStep μ B
  let P := bandPad u
  let d := fourPhaseDepth u
  let a := innerBandLow u
  let b := innerBandHigh u
  let qs := bandProtectedNodes κ B μ u h
  let χ := bandHeightWeight μ u
  let ε := 3*((d:ℝ)+2)*Real.log rho/Real.sqrt u
  let Z := fun q : ParentedScheduleNode => nodePaddedHeight φ P q.node
  let Δ := fun q : ParentedScheduleNode => paddedRootDecrease φ P q.node.reserve q.node.source
  let χe := fun q : ParentedScheduleNode => smoothedBandWeight u (u/bandRatio) (Real.log q.node.pivot)
  let f := fun q : ParentedScheduleNode => χe q*Δ q
  let g := fun q : ParentedScheduleNode => (Δ q/(silverKernelMass d*Real.exp (nu*Z q)))*
    (∫ y in a..b, χ y*(silverAveragingKernel d (y-Z q)*Real.exp (nu*y)))
  have hLip : 0 ≤ 3/Real.sqrt u := div_nonneg (by norm_num) (Real.sqrt_nonneg u)
  have hε : 0 ≤ ε := by dsimp only [ε]; have hω := log_rho_positive; positivity
  have hPred (q : ParentedScheduleNode) (hq : q ∈ qs) : bandProtectedPredicate B μ u q.node := by
    change q ∈ bandProtectedNodes κ B μ u h at hq
    rw [bandProtectedNodes_eq] at hq
    have hh := (List.mem_filter.mp hq).2
    exact @of_decide_eq_true _ (Classical.propDecidable _) hh
  have hEach : ∀ q ∈ qs, |f q-g q| ≤ ε*|Δ q| := by
    intro q hq
    have hKernel := silver_kernel_convolution_error d (Z q) a b (χe q) (Δ q) (3/Real.sqrt u) χ
      hGeometry.2.2.1 hLip (bandHeightWeight_continuous S.mu_positive)
      (fun hh => hSupport κ B cap μ critical h q.node S (hPred q hq) hh)
      (fun y _ => hDifference κ B cap μ critical y h q.node S (hPred q hq))
    have hCoeff : (3/Real.sqrt u)*(((d+2:ℕ):ℝ)*Real.log rho) = ε := by dsimp only [ε]; push_cast; ring
    rwa [hCoeff] at hKernel
  have hSum := list_abs_sum_sub_le f g (fun q => ε*|Δ q|) qs hEach
  rw [List.sum_map_mul_left] at hSum
  have hConvolution := (bandKernelConvolution_integral (κ:=κ) (B:=B) (u:=u) (a:=a) (b:=b) h S.mu_positive).2
  have hNorm : (∫ y in a..b, bandKernelConvolution κ B μ u h y)/silverKernelMass d = (qs.map g).sum := by
    rw [hConvolution,div_eq_mul_inv,← List.sum_map_mul_right]
    congr 1
    apply List.map_congr_left
    intro q hq
    dsimp only [g,Δ,Z,φ,P,d]
    field_simp [Real.exp_ne_zero,(silverKernelMass_positive (fourPhaseDepth u)).ne'] <;> ring
  have hAbs := hAbsolute κ B cap μ critical h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa S.scale_upper
    S.curvature_lower S.curvature_upper S.curvature_half S.noncritical S.critical_charge S.critical_rank S.distance_stable S.threshold_count S.rank_lower
  have hGainNonneg : 0 ≤ (qs.map fun q => Real.exp (nu*parentedHeight φ P q)*|paddedRootGain φ P q.node.reserve q.node.source|).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hPower : (qs.map fun q => |Δ q|).sum ≤ Ca*weightedCount h cap := by
    dsimp only [qs,Δ,φ,P] at hGainNonneg ⊢
    linarith only [hAbs,hGainNonneg]
  have hPowerScale := mul_le_mul_of_nonneg_left hPower hε
  have hRateScale := mul_le_mul_of_nonneg_right hRate (show 0 ≤ Ca*weightedCount h cap by have hw := weightedCount_nonneg h cap; positivity)
  rw [hNorm]
  change |(qs.map f).sum-(qs.map g).sum| ≤ _
  dsimp only [ε,d] at hSum hPowerScale
  linear_combination hSum+hPowerScale+hRateScale

end
end StrongSilver
