-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutMasses
import StrongSilver.Constants
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

theorem cutPower_eq_phase_sum (φ : ℝ → ℝ) (P reserve : ℝ) (C : ScheduleCut) :
    cutPower φ P reserve C = (C.phases.map fun q => (gapPrefix φ q.gap+P)^nu).sum+
      (gapPrefix φ C.terminal+P+reserve)^nu := by
  simp only [cutPower,cutMasses,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,List.map_map,Function.comp_def]

theorem cutPower_pad_mono (φ : ℝ → ℝ) {P Q reserve : ℝ} (hP : 0 ≤ P) (hPQ : P ≤ Q)
    (hr : 0 ≤ reserve) (C : ScheduleCut) : cutPower φ P reserve C ≤ cutPower φ Q reserve C := by
  rw [cutPower_eq_phase_sum,cutPower_eq_phase_sum]
  apply add_le_add
  · apply List.sum_le_sum
    intro q _
    exact Real.rpow_le_rpow (add_nonneg (gapPrefix_nonnegative φ q.gap) hP) (add_le_add le_rfl hPQ) nu_positive.le
  · exact Real.rpow_le_rpow (add_nonneg (add_nonneg (gapPrefix_nonnegative φ C.terminal) hP) hr)
      (add_le_add (add_le_add le_rfl hPQ) le_rfl) nu_positive.le

theorem phase_power_pad_increment (φ : ℝ → ℝ) {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (qs : List CutPhase) :
    (qs.map fun q => (gapPrefix φ q.gap+(P+Q))^nu).sum ≤
      (qs.map fun q => (gapPrefix φ q.gap+P)^nu).sum+(qs.length : ℝ)*Q^nu := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have hh := Real.rpow_add_le_add_rpow (add_nonneg (gapPrefix_nonnegative φ q.gap) hP) hQ nu_positive.le nu_lt_one.le
    rw [add_assoc] at hh
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hh,ih]

theorem cutPower_pad_increment (φ : ℝ → ℝ) {P Q reserve : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hr : 0 ≤ reserve) (C : ScheduleCut) :
    cutPower φ (P+Q) reserve C ≤ cutPower φ P reserve C+((C.phases.length : ℝ)+1)*Q^nu := by
  have hs := phase_power_pad_increment φ hP hQ C.phases
  have ht := Real.rpow_add_le_add_rpow (add_nonneg (add_nonneg (gapPrefix_nonnegative φ C.terminal) hP) hr)
    hQ nu_positive.le nu_lt_one.le
  have he : gapPrefix φ C.terminal+P+reserve+Q = gapPrefix φ C.terminal+(P+Q)+reserve := by ring
  rw [he] at ht
  rw [cutPower_eq_phase_sum,cutPower_eq_phase_sum]
  nlinarith only [hs,ht]

theorem cutPower_reserve_increment (φ : ℝ → ℝ) {P reserve Q : ℝ} (hP : 0 ≤ P) (hr : 0 ≤ reserve)
    (hQ : 0 ≤ Q) (C : ScheduleCut) :
    cutPower φ P (reserve+Q) C ≤ cutPower φ P reserve C+Q^nu := by
  have ht := Real.rpow_add_le_add_rpow (add_nonneg (add_nonneg (gapPrefix_nonnegative φ C.terminal) hP) hr)
    hQ nu_positive.le nu_lt_one.le
  rw [add_assoc] at ht
  rw [cutPower_eq_phase_sum,cutPower_eq_phase_sum]
  linarith only [ht]

/-- Removing the common pad and the terminal reserve charges each original
cut gap once and charges the terminal reserve once. -/
theorem cutPower_remove_padding (φ : ℝ → ℝ) {P κ H : ℝ} (hP : 0 ≤ P) (hκ : 0 ≤ κ)
    (C : ScheduleCut) (hH : H ≤ cutPower φ P κ C) :
    H-((C.phases.length : ℝ)+1)*P^nu-κ^nu ≤ cutPower φ 1 0 C := by
  have hm := cutPower_pad_mono φ hP (show P ≤ 1+P by linarith) hκ C
  have hp := cutPower_pad_increment φ (by norm_num : (0 : ℝ) ≤ 1) hP hκ C
  have hr := cutPower_reserve_increment φ (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0) hκ C
  simp only [zero_add] at hr
  linarith only [hH,hm,hp,hr]

end
end StrongSilver
