-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AveragingScales
import StrongSilver.FinalScalePower

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 2200000

def bandRatio : ℝ := 1+firstAverageEta/2000

theorem bandRatio_bounds : 1 < bandRatio ∧ bandRatio < 2 := by
  have hh := firstAverageEta_bounds
  unfold bandRatio
  constructor <;> linarith only [hh.1,hh.2]

theorem bandRatio_gap_bounds : 0 < bandRatio-1 ∧ bandRatio-1 < (1/1000)*firstAverageEta := by
  have hh := firstAverageEta_bounds.1
  unfold bandRatio
  constructor <;> linarith only [hh]

/-- Every possible final averaging window below r*Y stays below the
cutoff where the preceding linear mass estimate is negligible. -/
theorem eventually_final_average_window : ∀ᶠ R : ℝ in atTop, ∀ B : ℝ,
    1 ≤ B → R ≤ B^nu → ∀ v : ℝ, finalAverageLogScale R ≤ v → v ≤ bandRatio*finalAverageLogScale R →
    ∀ t ∈ Icc (0 : ℝ) 1,
      1 ≤ Real.exp (v+t*Real.sqrt v) ∧ Real.exp (v+t*Real.sqrt v) ≤ B ∧
        Real.exp (v+t*Real.sqrt v) ≤ R^finalCutoffExponent := by
  have hr := bandRatio_bounds
  have hd : 0 < 2-bandRatio := sub_pos.mpr hr.2
  have hd2 : 0 < (2-bandRatio)^2 := sq_pos_of_pos hd
  filter_upwards [eventually_gt_atTop (1 : ℝ),finalAverageLogScale_escape.eventually_ge_atTop (1 : ℝ),
    finalAverageLogScale_escape.eventually_ge_atTop (bandRatio/(2-bandRatio)^2)] with R hR hY hlarge
  intro B hB hRB v hYv hvY t ht
  have hR0 := zero_lt_one.trans hR
  have hB0 := zero_lt_one.trans_le hB
  have hY0 : 0 ≤ finalAverageLogScale R := (by norm_num : (0 : ℝ) ≤ 1).trans hY
  have hlarge' := mul_le_mul_of_nonneg_left hlarge hd2.le
  have he : (2-bandRatio)^2*(bandRatio/(2-bandRatio)^2) = bandRatio := by field_simp
  rw [he] at hlarge'
  have hprod := mul_le_mul_of_nonneg_right hlarge' hY0
  have hroot : Real.sqrt (bandRatio*finalAverageLogScale R) ≤ (2-bandRatio)*finalAverageLogScale R := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hd.le hY0)).mp
    rw [Real.sq_sqrt (mul_nonneg (zero_lt_one.trans hr.1).le hY0)]
    nlinarith only [hprod]
  have hvsqrt := (Real.sqrt_le_sqrt hvY).trans hroot
  have ht0 := mul_nonneg ht.1 (Real.sqrt_nonneg v)
  have ht1 := mul_le_mul_of_nonneg_right ht.2 (Real.sqrt_nonneg v)
  have hs0 : 0 ≤ v+t*Real.sqrt v := by linarith only [hY0,hYv,ht0]
  have hs2 : v+t*Real.sqrt v ≤ 2*finalAverageLogScale R := by nlinarith only [hvY,hvsqrt,ht1]
  have hExp : Real.exp (2*finalAverageLogScale R) = R^finalCutoffExponent := by
    rw [Real.rpow_def_of_pos hR0]
    congr 1
    unfold finalAverageLogScale finalCutoffExponent
    field_simp
    <;> ring
  have hfinal := (Real.exp_le_exp.mpr hs2).trans_eq hExp
  have hnu : nu*finalCutoffExponent = (1 : ℝ)/2 := by
    unfold finalCutoffExponent
    have hn := nu_positive.ne'
    field_simp
  have hp := Real.rpow_le_rpow hR0.le hRB finalCutoffExponent_bounds.1.le
  rw [← Real.rpow_mul hB0.le,hnu] at hp
  have hhalf : B^((1 : ℝ)/2) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB (by norm_num : (1 : ℝ)/2 ≤ 1)
  exact ⟨Real.one_le_exp_iff.mpr hs0,hfinal.trans (hp.trans hhalf),hfinal⟩

end
end StrongSilver
