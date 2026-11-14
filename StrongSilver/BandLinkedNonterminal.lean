-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFollowingProperties
import StrongSilver.BandGoodChildGeometry

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter
noncomputable section
set_option maxHeartbeats 5000000

/-- Every actual good linked gap has a following selected pivot. A
terminal gap keeps reserve kappa, whereas a balanced band node has
reserve zero. -/
theorem eventually_band_good_linked_nonterminal : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y : ℝ, ∀ h : List ℝ, ∀ q : LinkedGap,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    q ∈ linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h) →
    bandGoodBool B μ u q.node = true → ∃ p, q.following = some p := by
  filter_upwards [eventually_band_good_parent_geometry] with u H
  intro κ B μ y h q hκ hB hBκ hU hμ hμB hq hGood
  have hInt := bandGoodBool_internal hGood
  have hMem := linkedFrontier_internal_mem hq hInt
  have hZero := (H κ B μ h q.node hκ hB hBκ hU hμ hμB hMem hGood).1
  cases hp : q.following with
  | none =>
    have hReserve := (linkedFrontier_following_none_reserve hq hp).2
    have hh : κ = 0 := hReserve.symm.trans hZero
    exact False.elim (ne_of_gt hκ hh)
  | some p => exact ⟨p,rfl⟩

end
end StrongSilver
