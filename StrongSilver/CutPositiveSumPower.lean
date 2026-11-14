-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutLogRankUpper
import StrongSilver.CutPowerRankUpper

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

/-- Scaled power bound from the original positive-mass budget. It
applies to both signed-prefix and positive-sum cut masses. -/
theorem cut_power_scaled_prefix_bound (φ : ℝ → ℝ) {A P κ : ℝ} (hA : 0 < A)
    (hP : 0 < P) (hκ : 0 ≤ κ) (C : ScheduleCut)
    (hmass : (C.phases.map fun q => gapPrefix φ q.gap).sum+gapPrefix φ C.terminal ≤ 2*positiveMass C.unselected) :
    cutPower φ P κ C ≤ ((C.phases.length:ℝ)+1)*A^nu+
      (2*positiveMass C.unselected+((C.phases.length:ℝ)+1)*P)*A^(nu-1)+κ^nu := by
  have hs := list_scaled_power_upper hA (cutMasses φ P 0 C)
    (fun x hx => (cutMasses_positive φ hP (by norm_num) C x hx).le)
  rw [cutMasses_length,Nat.cast_add,Nat.cast_one] at hs
  have hsum : (cutMasses φ P 0 C).sum ≤ 2*positiveMass C.unselected+((C.phases.length:ℝ)+1)*P := by
    rw [cutMasses_sum]
    linarith only [hmass]
  have hp := mul_le_mul_of_nonneg_right hsum (Real.rpow_pos_of_pos hA (nu-1)).le
  have hr := cutPower_reserve_increment φ hP.le (by norm_num : (0:ℝ) ≤ 0) hκ C
  simp only [zero_add] at hr
  change cutPower φ P 0 C ≤ _ at hs
  linear_combination hs+hp+hr

theorem full_cut_power_rank_upper_of_prefix_bound (φ : ℝ → ℝ) {A B P κ cap : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hAcap : A ≤ cap) (hP : 0 < P) (hPA : P ≤ A) (hκ : 0 ≤ κ)
    (hprefix : ∀ g : List ℝ, (∀ b ∈ g, b ≤ B) → gapPrefix φ g ≤ 2*positiveMass g)
    (h : List ℝ) (hcount : 1 ≤ countAbove h A) :
    cutPower φ P κ (fullCut A h) ≤ (4+2/(1-nu))*weightedCount h cap+κ^nu := by
  let C := fullCut A h
  have hgap : ∀ b ∈ C.unselected, b ≤ A := fun b hb => fullCut_unselected hb
  have hp : ∀ q ∈ C.phases, gapPrefix φ q.gap ≤ 2*positiveMass q.gap := fun q hq =>
    hprefix q.gap (fun b hb => (hgap b (ScheduleCut.mem_gap_unselected hq hb)).trans hAB)
  have ht := hprefix C.terminal (fun b hb => (hgap b (ScheduleCut.mem_terminal_unselected hb)).trans hAB)
  have hmass := cut_prefix_sum_mass_bound φ C hp ht
  have hs := cut_power_scaled_prefix_bound φ hA hP hκ C hmass
  have hk := full_cut_gap_count_rank hA hAcap h hcount
  have hm := C.unselected_positiveMass_rank_bound hA hAcap (fun b hb _ => hgap b hb)
  have hword : C.word = h := cutSchedule_word _ _
  rw [hword] at hm
  have hp0 := Real.rpow_pos_of_pos hA nu
  have hp1 := Real.rpow_pos_of_pos hA (nu-1)
  have hcount0 : 0 ≤ (C.phases.length:ℝ)+1 := by positivity
  have hkp := mul_le_mul_of_nonneg_right hPA hcount0
  have hpad := mul_le_mul_of_nonneg_right hkp hp1.le
  have hmassPrice := mul_le_mul_of_nonneg_right hm (show 0 ≤ 2*A^(nu-1) by positivity)
  have hselected := mul_le_mul_of_nonneg_right hk hp0.le
  have hcancel : A^(-nu)*A^nu = 1 := by rw [← Real.rpow_add hA,neg_add_cancel,Real.rpow_zero]
  have hmasscancel : A^(1-nu)*A^(nu-1) = 1 := by
    rw [← Real.rpow_add hA,show 1-nu+(nu-1) = (0:ℝ) by ring,Real.rpow_zero]
  have hAprod : A*A^(nu-1) = A^nu := by
    calc
      _ = A^(1:ℝ)*A^(nu-1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hA]; congr 1; ring
  have hselected' : ((C.phases.length:ℝ)+1)*A^nu ≤ 2*weightedCount h cap := by
    calc
      _ ≤ 2*weightedCount h cap*(A^(-nu)*A^nu) := by linear_combination hselected
      _ = _ := by rw [hcancel,mul_one]
  have hmass' : 2*positiveMass C.unselected*A^(nu-1) ≤ (2/(1-nu))*weightedCount h cap := by
    calc
      _ ≤ (2/(1-nu))*weightedCount h cap*(A^(1-nu)*A^(nu-1)) := by linear_combination hmassPrice
      _ = _ := by rw [hmasscancel,mul_one]
  have hpad' : ((C.phases.length:ℝ)+1)*P*A^(nu-1) ≤ 2*weightedCount h cap := by
    calc
      _ ≤ ((C.phases.length:ℝ)+1)*(A*A^(nu-1)) := by linear_combination hpad
      _ = _ := by rw [hAprod]
      _ ≤ _ := hselected'
  linear_combination hs+hselected'+hmass'+hpad'

/-- P <= P^S <= C*W at every actual full working cut (up to the explicit
terminal reserve power), with no schedule nonnegativity assumption. -/
theorem full_cut_positive_sum_power_rank_upper {μ A B P κ cap : ℝ} (hμ : 0 < μ) (hA : 0 < A) (hB : 0 < B)
    (hAB : A ≤ B) (hAcap : A ≤ cap) (hcap : μ*B ≤ 1/2) (hP : 0 < P) (hPA : P ≤ A) (hκ : 0 ≤ κ)
    (h : List ℝ) (hcount : 1 ≤ countAbove h A) :
    cutPower (cappedStep μ B) P κ (fullCut A h) ≤
      cutPower (positivePartStep (cappedStep μ B)) P κ (fullCut A h) ∧
    cutPower (positivePartStep (cappedStep μ B)) P κ (fullCut A h) ≤
      (4+2/(1-nu))*weightedCount h cap+κ^nu := by
  exact ⟨cutPower_le_positivePart _ hP.le hκ _,
    full_cut_power_rank_upper_of_prefix_bound _ hA hAB hAcap hP hPA hκ
      (fun g hg => positivePart_capped_gapPrefix_le_mass hμ hB hcap g hg) h hcount⟩

end
end StrongSilver
