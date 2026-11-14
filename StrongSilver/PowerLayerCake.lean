-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LayerCake

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 2000000

def powerKernel (t : ℝ) : ℝ := nu*t^(nu-1)
def cappedPowerAbove (A B b : ℝ) : ℝ := if A ≤ b then (min b B)^nu else 0
def powerMoment (h : List ℝ) (A B : ℝ) : ℝ := (h.map (cappedPowerAbove A B)).sum

theorem powerKernel_continuousOn {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    ContinuousOn powerKernel (uIcc A B) := by
  rw [uIcc_of_le hAB]
  intro t ht
  have ht0 := hA.trans_le ht.1
  exact ((Real.continuousAt_rpow_const t (nu-1) (Or.inl ht0.ne')).const_mul nu).continuousWithinAt

theorem power_weighted_indicator_integrable {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (b : ℝ) :
    IntervalIntegrable (fun t => powerKernel t*thresholdIndicator b t) volume A B :=
  (thresholdIndicator_integrable b A B).continuousOn_mul (powerKernel_continuousOn hA hAB)

theorem power_weighted_count_integrable {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (h : List ℝ) :
    IntervalIntegrable (fun t => powerKernel t*(countAbove h t : ℝ)) volume A B :=
  (countAbove_integrable h A B).continuousOn_mul (powerKernel_continuousOn hA hAB)

theorem integral_powerKernel (A B : ℝ) : (∫ t in A..B, powerKernel t) = B^nu-A^nu := by
  have hν : -1 < nu-1 := by linarith only [nu_positive]
  unfold powerKernel
  rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl hν),show nu-1+1 = nu by ring]
  field_simp [nu_positive.ne']

theorem capped_power_point_identity {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (b : ℝ) :
    cappedPowerAbove A B b = A^nu*thresholdIndicator b A+
      ∫ t in A..B, powerKernel t*thresholdIndicator b t := by
  by_cases hb : A ≤ b
  · let c := min b B
    have hAc : A ≤ c := le_min hb hAB
    have hcB : c ≤ B := min_le_right _ _
    have he : (∫ t in A..B, powerKernel t*thresholdIndicator b t) =
        ∫ t in A..B, ({t : ℝ | t ≤ c}).indicator powerKernel t := by
      apply intervalIntegral.integral_congr_uIoo
      intro t ht
      rw [uIoo_of_le hAB] at ht
      have hiff : t ≤ b ↔ t ≤ c := ⟨fun htb => le_min htb ht.2.le,fun htc => htc.trans (min_le_left _ _)⟩
      simp only [thresholdIndicator,Set.indicator,Set.mem_setOf_eq,hiff]
      split_ifs <;> simp
    rw [he,intervalIntegral.integral_indicator ⟨hAc,hcB⟩,integral_powerKernel]
    simp only [cappedPowerAbove,thresholdIndicator,if_pos hb,mul_one]
    dsimp only [c]
    ring
  · have he : (∫ t in A..B, powerKernel t*thresholdIndicator b t) = 0 := by
      calc
        _ = ∫ _t in A..B, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_uIoo
          intro t ht
          rw [uIoo_of_le hAB] at ht
          have hn : ¬ t ≤ b := by linarith only [ht.1,hb]
          simp only [thresholdIndicator,if_neg hn,mul_zero]
        _ = 0 := intervalIntegral.integral_zero
    rw [he]
    simp only [cappedPowerAbove,thresholdIndicator,if_neg hb,mul_zero,zero_add]

/-- Layer cake for the truncated nu-power moment, including boundary ties. -/
theorem powerMoment_eq_layerCake {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (h : List ℝ) :
    powerMoment h A B = A^nu*(countAbove h A : ℝ)+
      ∫ t in A..B, powerKernel t*(countAbove h t : ℝ) := by
  induction h with
  | nil => simp [powerMoment,countAbove]
  | cons b h ih =>
    simp only [powerMoment,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih,capped_power_point_identity hA hAB b]
    simp_rw [real_countAbove_cons,mul_add]
    rw [intervalIntegral.integral_add (power_weighted_indicator_integrable hA hAB b) (power_weighted_count_integrable hA hAB h)]
    ring

end
end StrongSilver
