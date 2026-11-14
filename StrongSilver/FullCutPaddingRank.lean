-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PhaseMarkingBudget
import StrongSilver.CutPowerPadding
import StrongSilver.InitialThresholdBand

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

theorem fullCut_count_le_countAbove (h : List ℝ) (A : ℝ) :
    ((fullCut A h).phases.length : ℝ) ≤ (countAbove h A : ℝ) := by
  have hh := (fullCut A h).pivot_count_weight_le A
  have he : ((fullCut A h).phases.map fun q => if A ≤ q.pivot then (1 : ℝ) else 0).sum =
      ((fullCut A h).phases.length : ℝ) := by
    have hm : (fullCut A h).phases.map (fun q => if A ≤ q.pivot then (1 : ℝ) else 0) =
        (fullCut A h).phases.map (fun _ => (1 : ℝ)) := by
      apply List.map_congr_left
      intro q hq
      exact if_pos (fullCut_pivot hq).le
    rw [hm]
    simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one]
  rw [he] at hh
  simpa only [fullCut,cutSchedule_word] using hh

theorem full_cut_gap_count_rank {A cap : ℝ} (hA : 0 < A) (hcap : A ≤ cap) (h : List ℝ)
    (hcount : 1 ≤ countAbove h A) :
    ((fullCut A h).phases.length : ℝ)+1 ≤ 2*weightedCount h cap*A^(-nu) := by
  have hk := fullCut_count_le_countAbove h A
  have hr := countAbove_rank_bound h hA hcap
  have hc : (1 : ℝ) ≤ (countAbove h A : ℝ) := by exact_mod_cast hcount
  nlinarith only [hk,hr,hc]

theorem full_cut_pad_rank_charge {A B cap ξ : ℝ} (hA : 0 < A) (hB : 0 < B) (hcap : A ≤ cap)
    (hfloor : B^(1-ξ) ≤ A) (h : List ℝ) (hcount : 1 ≤ countAbove h A) :
    (((fullCut A h).phases.length : ℝ)+1)*(B^((987 : ℝ)/1000))^nu ≤
      2*weightedCount h cap*B^((ξ-(13 : ℝ)/1000)*nu) := by
  have hk := full_cut_gap_count_rank hA hcap h hcount
  have hpow := mul_le_mul_of_nonneg_right hk (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hB ((987 : ℝ)/1000)) nu).le
  have hfloor0 := Real.rpow_pos_of_pos hB (1-ξ)
  have hAinv : A^(-nu) ≤ (B^(1-ξ))^(-nu) :=
    Real.rpow_le_rpow_of_nonpos hfloor0 hfloor (neg_nonpos.mpr nu_positive.le)
  have hh := mul_le_mul_of_nonneg_left hAinv (show 0 ≤ 2*weightedCount h cap*(B^((987 : ℝ)/1000))^nu by
    have hw := weightedCount_nonneg h cap
    positivity)
  have he : (B^(1-ξ))^(-nu)*(B^((987 : ℝ)/1000))^nu = B^((ξ-(13 : ℝ)/1000)*nu) := by
    rw [← Real.rpow_mul hB.le,← Real.rpow_mul hB.le,← Real.rpow_add hB]
    congr 1
    ring
  calc
    _ ≤ 2*weightedCount h cap*A^(-nu)*(B^((987 : ℝ)/1000))^nu := hpow
    _ ≤ 2*weightedCount h cap*((B^(1-ξ))^(-nu)*(B^((987 : ℝ)/1000))^nu) := by linear_combination hh
    _ = _ := by rw [he]

theorem full_cut_remove_padding_rank (φ : ℝ → ℝ) {A B cap ξ κ H : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hcap : A ≤ cap) (hfloor : B^(1-ξ) ≤ A) (hκ : 0 ≤ κ)
    (h : List ℝ) (hcount : 1 ≤ countAbove h A)
    (hH : H ≤ cutPower φ (B^((987 : ℝ)/1000)) κ (fullCut A h)) :
    H-2*weightedCount h cap*B^((ξ-(13 : ℝ)/1000)*nu)-κ^nu ≤ cutPower φ 1 0 (fullCut A h) := by
  have hh := cutPower_remove_padding φ (Real.rpow_pos_of_pos hB _).le hκ (fullCut A h) hH
  have hp := full_cut_pad_rank_charge hA hB hcap hfloor h hcount
  linarith only [hh,hp]

end
end StrongSilver
