-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedGoodDepthSpacing
import StrongSilver.GoodDepthEnvelope

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6200000

/-- The exact silver identity converts a path of k good edges into
an O(2^k) weight ratio. The accumulated band-tolerance error is uniform
for every k up to d+2. -/
theorem eventually_band_depth_weight_factor : ∀ᶠ u : ℝ in atTop,
    ∀ k : ℕ, k ≤ fourPhaseDepth u+2 →
    Real.exp (nu*((k:ℝ)*Real.log rho+(k:ℝ)*(11*bandTolerance u))) ≤ Real.exp 11*(2:ℝ)^k := by
  filter_upwards [eventually_band_depth_tolerance (by norm_num : (0:ℝ) < 1),eventually_gt_atTop (0:ℝ)] with u hTol hu
  intro k hk
  have hδ := (Real.rpow_pos_of_pos hu (-(1:ℝ)/10)).le
  change 0 ≤ bandTolerance u at hδ
  have hkr : (k:ℝ) ≤ (fourPhaseDepth u:ℝ)+4 := by exact_mod_cast (show k ≤ fourPhaseDepth u+4 by omega)
  have hkd := (mul_le_mul_of_nonneg_right hkr hδ).trans hTol
  have hprod : 0 ≤ (k:ℝ)*bandTolerance u := mul_nonneg (Nat.cast_nonneg _) hδ
  have hν : nu ≤ 1 := nu_lt_one.le
  have hνprod := mul_le_mul_of_nonneg_right hν hprod
  have herr : nu*((k:ℝ)*(11*bandTolerance u)) ≤ 11 := by nlinarith only [hkd,hνprod]
  have hbase : Real.exp (nu*Real.log rho) = 2 := by
    simpa only [Real.rpow_def_of_pos rho_positive,mul_comm] using rho_rpow_nu
  have hEq : Real.exp (nu*((k:ℝ)*Real.log rho+(k:ℝ)*(11*bandTolerance u))) =
      (2:ℝ)^k*Real.exp (nu*((k:ℝ)*(11*bandTolerance u))) := by
    rw [mul_add,show nu*((k:ℝ)*Real.log rho) = (k:ℝ)*(nu*Real.log rho) by ring,Real.exp_add,Real.exp_nat_mul,hbase]
  rw [hEq]
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr herr) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)
  exact hh.trans_eq (by ring)

/-- The weighted cutoff envelope estimate used in (4.24), on the
actual original indexed schedule tree. The source balance, height
spacing and unique-ancestor hypotheses are all discharged. -/
theorem eventually_band_depth_transport : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ a b : ℝ, ∀ h : List ℝ, ∀ k : ℕ, ∀ F : ScheduleNode → ℝ,
    0 ≤ κ → 1 < B → μ*B ≤ 1/2 → a ≤ b → k ≤ fourPhaseDepth u+2 → (∀ q, 0 ≤ F q) →
    (∫ y in a..b, goodDepthEnvelope (bandGoodBool B μ u) (nodePaddedHeight (cappedStep μ B) (bandPad u)) F
      nu (Real.log rho+11*bandTolerance u) k ((cartesian h).indexedTree 0 κ) y) ≤
      C*(2:ℝ)^k*((BinaryForest.labels ((cartesian h).indexedTree 0 κ)).map fun q =>
        Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q)*F q).sum := by
  let C := Real.exp (Real.log rho+22)/nu
  have hC : 0 < C := div_pos (Real.exp_pos _) nu_positive
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_band_good_edge_deviation,eventually_band_depth_weight_factor,eventually_band_forest_spacing]
    with u hEdges hFactor hTol
  intro κ B μ a b h k F hκ hB hμB hab hk hF
  let G := bandGoodBool B μ u
  let H := nodePaddedHeight (cappedStep μ B) (bandPad u)
  let t := (cartesian h).indexedTree 0 κ
  let S := ((BinaryForest.labels t).map fun q => Real.exp (nu*H q)*F q).sum
  have hS : 0 ≤ S := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (Real.exp_pos _).le (hF q)
  have hE := goodDepthEnvelope_integral_upper G H F nu (Real.log rho+11*bandTolerance u) a b
    nu_positive.le hF hab k t
  have hD := weighted_good_depth_total G H F nu (Real.log rho) (11*bandTolerance u)
    nu_positive.le hF k t (hEdges κ B μ h hκ hB hμB)
  have hFdepth := hFactor k hk
  have hL : Real.exp (nu*(Real.log rho+11*bandTolerance u)) ≤ Real.exp (Real.log rho+11) := by
    apply Real.exp_le_exp.mpr
    have hω := log_rho_positive
    have hδ := hTol.1
    have hδ1 : bandTolerance u ≤ 1 := hTol.2.1.trans (by norm_num)
    have hPos : 0 ≤ Real.log rho+11*bandTolerance u := by positivity
    have hh := mul_le_mul_of_nonneg_right nu_lt_one.le hPos
    nlinarith only [hh,hδ1]
  have hD' := mul_le_mul_of_nonneg_right hFdepth hS
  have hDS := hD.trans hD'
  have hScale := mul_le_mul_of_nonneg_left hDS (Real.exp_pos (nu*(Real.log rho+11*bandTolerance u))).le
  have hCoeff := mul_le_mul_of_nonneg_right hL
    (mul_nonneg (Real.exp_pos (11:ℝ)).le (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k) hS))
  have hExp : Real.exp (Real.log rho+11)*Real.exp 11 = Real.exp (Real.log rho+22) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hFinal : nu*(∫ y in a..b, goodDepthEnvelope G H F nu (Real.log rho+11*bandTolerance u) k t y) ≤
      Real.exp (Real.log rho+22)*(2:ℝ)^k*S := by
    dsimp only [S] at hCoeff
    rw [show Real.exp (Real.log rho+11)*(Real.exp 11*((2:ℝ)^k*S)) =
      (Real.exp (Real.log rho+11)*Real.exp 11)*(2:ℝ)^k*S by ring,hExp] at hCoeff
    dsimp only [S] at hScale
    linear_combination hE+hScale+hCoeff
  calc
    _ ≤ (Real.exp (Real.log rho+22)*(2:ℝ)^k*S)/nu :=
      (le_div_iff₀ nu_positive).mpr (by linear_combination hFinal)
    _ = C*(2:ℝ)^k*S := by dsimp only [C]; ring

end
end StrongSilver
