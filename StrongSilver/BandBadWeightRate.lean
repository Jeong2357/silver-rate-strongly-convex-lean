-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandBadWeightBudget

namespace StrongSilver
open ScheduleTree Filter Real
noncomputable section
set_option maxHeartbeats 3600000

local instance (φ : ℝ → ℝ) (P κ δ : ℝ) (t : ScheduleTree) : Decidable (PaddedGood φ P κ δ t) := Classical.propDecidable _

def bandTolerance (u : ℝ) : ℝ := u^(-(1:ℝ)/10)

theorem eventually_band_bad_weight_rate : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    ((bandProtectedNodes κ B μ u h).map fun q =>
      if PaddedGood (cappedStep μ B) (bandPad u) q.node.reserve (bandTolerance u) q.node.source then 0 else
        Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).sum ≤
      C*weightedCount h cap*u^((1:ℝ)/5) := by
  obtain ⟨C,hC,H⟩ := eventually_band_bad_weight_budget
  have ht := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/10)
  refine ⟨C,hC,?_⟩
  filter_upwards [H,eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4))] with u Hu hu hδ
  intro κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hδ0 : 0 < bandTolerance u := Real.rpow_pos_of_pos hu _
  have hδmax : bandTolerance u ≤ 1/4 := by simpa only [bandTolerance,neg_div] using hδ.le
  have hh := Hu κ B cap μ critical (bandTolerance u) h hκ hB hBcap hcapκ hU hμ hμu hμB hδ0.le hδmax
    hcrit hcritical hcriticalRank hD hcount hκW
  have hp : 0 ≤ u^((1:ℝ)/5) := (Real.rpow_pos_of_pos hu _).le
  have hm := mul_le_mul_of_nonneg_right hh hp
  have hid : (bandTolerance u)^2*u^((1:ℝ)/5) = 1 := by
    unfold bandTolerance
    rw [pow_two,← Real.rpow_add hu,← Real.rpow_add hu]
    norm_num
  have hEq (S : ℝ) : ((bandTolerance u)^2*S)*u^((1:ℝ)/5) = S := by
    calc
      _ = ((bandTolerance u)^2*u^((1:ℝ)/5))*S := by ring
      _ = S := by rw [hid,one_mul]
  rwa [hEq] at hm

end
end StrongSilver
