-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandUnitPointwise
import StrongSilver.BandBadWeightRate
import StrongSilver.PaddedToSilverBalance

namespace StrongSilver
open ScheduleTree Real Filter
noncomputable section
set_option maxHeartbeats 3400000

/-- The numerical tolerance used in the paper dominates 1/u, which
already dominates the pad-to-time ratio throughout the outer band. -/
theorem inverse_le_bandTolerance {u : ℝ} (hu : 1 ≤ u) : 1/u ≤ bandTolerance u := by
  have hh := Real.rpow_le_rpow_of_exponent_le hu (by norm_num : (-1:ℝ) ≤ -(1:ℝ)/10)
  simpa only [bandTolerance,Real.rpow_neg_one,one_div] using hh

/-- The exact offset-one SilverBalanced hypothesis required by the
finite depth trajectory is proved for every balanced protected vertex. -/
theorem eventually_band_silver_balance : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ : ℝ, ∀ h : List ℝ, ∀ q : ParentedScheduleNode,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    bandTolerance u ≤ 1/4 → q ∈ bandProtectedNodes κ B μ u h →
    PaddedBalanced (cappedStep μ B) (bandPad u) q.node.reserve (bandTolerance u) q.node.source →
    SilverBalanced (cappedStep μ B) (4*bandTolerance u) q.node.source := by
  filter_upwards [eventually_band_balanced_nonterminal,eventually_band_pad_small,eventually_ge_atTop (1:ℝ)]
    with u hNonterminal hPad hu
  intro κ B μ h q hκ hB hBκ hU hμ hμB hδmax hq hb
  have hu0 := zero_lt_one.trans_le hu
  have hδ : 0 < bandTolerance u := Real.rpow_pos_of_pos hu0 _
  have hh := of_decide_eq_true (List.mem_filter.mp hq).2
  have hz := hNonterminal κ B μ (bandTolerance u) h q hκ hB hBκ hU hμ hμB hδ.le hδmax
    (List.mem_filter.mp hq).1 hh.2.1 hb
  have hratio := (hPad.2 _ hh.2.2.1.le).2.trans (inverse_le_bandTolerance hu)
  have he : Real.exp (parentedHeight (cappedStep μ B) (bandPad u) q) = cappedStep μ B q.node.pivot-bandPad u :=
    Real.exp_log (sub_pos.mpr hh.1)
  have hp := (div_le_iff₀ (Real.exp_pos _)).mp hratio
  rw [he] at hp
  have hpad : bandPad u ≤ bandTolerance u*cappedStep μ B q.node.source.rootStep := by
    have hx := mul_nonneg hδ.le (Real.exp_pos ((987:ℝ)/1000*u)).le
    change 0 ≤ bandTolerance u*bandPad u at hx
    dsimp only [ScheduleNode.pivot] at hp
    nlinarith only [hp,hx]
  rw [hz] at hb
  exact paddedBalanced_to_silverBalanced hPad.1 hδ.le (hδmax.trans (by norm_num)) hpad hb

end
end StrongSilver
