-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SpectralGains

namespace StrongSilver
open Complex Metric Real MeasureTheory Filter
noncomputable section

def negativeLogCharge (κ : ℝ) (h : List ℝ) : ℝ :=
  (h.map (fun b => if b < 0 then Real.log (1-b/κ) else 0)).sum

theorem arcsine_curvature_admissible {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128)
    (hκ : 0 < κ) (hcap : 1 ≤ a*κ) (z : ℂ) (hz : ‖z‖ = 1) :
    1/κ ≤ spectralCurvature (arcsineParameter a) (a*κ) z ∧
    spectralCurvature (arcsineParameter a) (a*κ) z ≤ 1 := by
  obtain ⟨hr,hr1⟩ := arcsineParameter_bounds ha ha1
  constructor
  · exact (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 8) hκ.le).trans
      (arcsine_curvature_lower ha ha1 hκ z hz)
  · have hu := (spectralCurvature_bounds hr.le hr1 (mul_pos ha hκ) z hz).2
    exact hu.trans ((div_le_one (mul_pos ha hκ)).mpr hcap)

theorem arcsine_step_charge {a κ b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128) (hκ : 0 < κ) :
    (if κ/2 ≤ b then Real.log 3 else 0)+(if b < 0 then Real.log (1-b/κ) else 0) ≤
      circleAverage (spectralStepLog (arcsineParameter a) (a*κ) b) 0 1+
        9*Real.sqrt a*(max 0 (min b (a*κ))/(a*κ)) := by
  obtain ⟨hr,hr1⟩ := arcsineParameter_bounds ha ha1
  have hB := mul_pos ha hκ
  have hcurv : ∀ z : ℂ, ‖z‖ = 1 → 1/κ ≤ spectralCurvature (arcsineParameter a) (a*κ) z := by
    intro z hz
    exact (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 8) hκ.le).trans
      (arcsine_curvature_lower ha ha1 hκ z hz)
  by_cases hb : b < 0
  · have hnlarge : ¬ κ/2 ≤ b := by linarith
    have hm : max 0 (min b (a*κ)) = 0 := max_eq_left ((min_le_left _ _).trans hb.le)
    simp only [hnlarge,hb,if_false,if_true,zero_add,hm,zero_div,mul_zero,add_zero]
    exact spectralStepLog_lower_negative hr hr1 hB hκ hb.le hcurv
  · have hnonneg : 0 ≤ b := le_of_not_gt hb
    by_cases hlarge : κ/2 ≤ b
    · have hlower := spectralStepLog_lower_large hr hr1 hB hκ hlarge
        (fun z hz => arcsine_curvature_lower ha ha1 hκ z hz)
      have hpos : 0 ≤ 9*Real.sqrt a*(max 0 (min b (a*κ))/(a*κ)) := by positivity
      simp only [hlarge,hb,if_true,if_false,add_zero]
      linarith
    · have hlower := arcsineStepLog_lower_capped ha ha1 hB hnonneg
      simp only [hlarge,hb,if_false,zero_add]
      linarith

theorem arcsine_schedule_charge {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128)
    (hκ : 0 < κ) (h : List ℝ) :
    Real.log 3*(countAbove h (κ/2) : ℝ)+negativeLogCharge κ h ≤
      circleAverage (spectralScheduleLog (arcsineParameter a) (a*κ) h) 0 1+
        9*Real.sqrt a*(clippedMass h (a*κ)/(a*κ)) := by
  rw [spectralScheduleLog_average]
  induction h with
  | nil => simp [negativeLogCharge,clippedMass]
  | cons b h ih =>
    have hb := arcsine_step_charge (b := b) ha ha1 hκ
    rw [countAbove_cons,Nat.cast_add]
    simp only [negativeLogCharge,clippedMass,List.map_cons,List.sum_cons] at ih ⊢
    rw [add_div]
    by_cases ht : κ/2 ≤ b
    · simp only [ht,if_true,Nat.cast_one] at hb ⊢
      nlinarith only [ih,hb]
    · simp only [ht,if_false,Nat.cast_zero] at hb ⊢
      nlinarith only [ih,hb]

/-- The arcsine average controls large and negative steps by the capped rank mass. -/
theorem large_negative_charge_bound {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128)
    (hκ : 0 < κ) (hcap : 1 ≤ a*κ) (h : List ℝ) (hD : D κ h ≤ 1) :
    Real.log 3*(countAbove h (κ/2) : ℝ)+negativeLogCharge κ h ≤
      (9/(1-nu))*Real.sqrt a*weightedCount h (a*κ)*(a*κ)^(-nu) := by
  obtain ⟨hr,hr1⟩ := arcsineParameter_bounds ha ha1
  have hB := mul_pos ha hκ
  have hupper := spectralScheduleLog_le_distance hr hr1 hB hκ
    (arcsine_curvature_admissible ha ha1 hκ hcap) h
  have hDr : (D κ h).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp) hD
  have hlog : Real.log (D κ h).toReal ≤ 0 := Real.log_nonpos (ENNReal.toReal_nonneg) hDr
  have hsum := arcsine_schedule_charge ha ha1 hκ h
  have hmass := clippedMass_rank_bound h hB le_rfl
  have hmassdiv := (div_le_div_of_nonneg_right hmass hB.le)
  have he : (weightedCount h (a*κ)*(a*κ)^(1-nu)/(1-nu))/(a*κ) =
      weightedCount h (a*κ)*(a*κ)^(-nu)/(1-nu) := by
    have hp : (a*κ)^(1-nu) = (a*κ)^(-nu)*(a*κ) := by
      rw [sub_eq_add_neg,add_comm,Real.rpow_add hB,Real.rpow_one]
    rw [hp]
    field_simp
  rw [he] at hmassdiv
  have hscaled := mul_le_mul_of_nonneg_left hmassdiv (by positivity : 0 ≤ 9*Real.sqrt a)
  calc
    _ ≤ 9*Real.sqrt a*(clippedMass h (a*κ)/(a*κ)) := by linarith
    _ ≤ 9*Real.sqrt a*(weightedCount h (a*κ)*(a*κ)^(-nu)/(1-nu)) := hscaled
    _ = _ := by ring

end
end StrongSilver
