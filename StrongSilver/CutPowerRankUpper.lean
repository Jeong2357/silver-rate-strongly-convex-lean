-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScaledPowerUpper
import StrongSilver.CutPowerCrudeUpper
import StrongSilver.FullCutPaddingRank

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2200000

theorem cutMasses_sum (φ : ℝ → ℝ) (P reserve : ℝ) (C : ScheduleCut) :
    (cutMasses φ P reserve C).sum = (C.phases.map fun q => gapPrefix φ q.gap).sum+
      gapPrefix φ C.terminal+((C.phases.length : ℝ)+1)*P+reserve := by
  simp only [cutMasses,List.sum_append,List.sum_cons,List.sum_nil,List.sum_map_add,
    List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one]
  ring

theorem capped_cutMasses_sum_bound {μ B : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hcap : μ*B ≤ 1/2)
    (P reserve : ℝ) (C : ScheduleCut) (hgap : ∀ b ∈ C.unselected, b ≤ B) :
    (cutMasses (cappedStep μ B) P reserve C).sum ≤ 2*Scalar.SignedIntervals.positiveMass C.unselected+
      ((C.phases.length : ℝ)+1)*P+reserve := by
  have hp : (C.phases.map fun q => gapPrefix (cappedStep μ B) q.gap).sum ≤
      2*(C.phases.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum := by
    have hh := List.sum_le_sum (l := C.phases) (f := fun q => gapPrefix (cappedStep μ B) q.gap)
      (g := fun q => 2*Scalar.SignedIntervals.positiveMass q.gap)
      (fun q hq => capped_gapPrefix_le_mass hμ hB hcap q.gap
        (fun b hb => hgap b (ScheduleCut.mem_gap_unselected hq hb)))
    simpa only [List.sum_map_mul_left] using hh
  have ht := capped_gapPrefix_le_mass hμ hB hcap C.terminal
    (fun b hb => hgap b (ScheduleCut.mem_terminal_unselected hb))
  rw [cutMasses_sum]
  have hm := C.unselected_positiveMass
  nlinarith only [hp,ht,hm]

theorem cut_power_scaled_mass_bound {μ A B P κ : ℝ} (hμ : 0 < μ) (hA : 0 < A) (hB : 0 < B)
    (hcap : μ*B ≤ 1/2) (hP : 0 < P) (hκ : 0 ≤ κ) (C : ScheduleCut) (hgap : ∀ b ∈ C.unselected, b ≤ B) :
    cutPower (cappedStep μ B) P κ C ≤ ((C.phases.length : ℝ)+1)*A^nu+
      (2*Scalar.SignedIntervals.positiveMass C.unselected+((C.phases.length : ℝ)+1)*P)*A^(nu-1)+κ^nu := by
  have hs := list_scaled_power_upper hA (cutMasses (cappedStep μ B) P 0 C)
    (fun x hx => (cutMasses_positive _ hP (by norm_num) C x hx).le)
  rw [cutMasses_length,Nat.cast_add,Nat.cast_one] at hs
  have hm := capped_cutMasses_sum_bound hμ hB hcap P 0 C hgap
  simp only [add_zero] at hm
  have hmass := mul_le_mul_of_nonneg_right hm (Real.rpow_pos_of_pos hA (nu-1)).le
  have hr := cutPower_reserve_increment (cappedStep μ B) hP.le (by norm_num : (0 : ℝ) ≤ 0) hκ C
  simp only [zero_add] at hr
  change cutPower (cappedStep μ B) P 0 C ≤ _ at hs
  linear_combination hs+hmass+hr

/-- Uniform O(W) power at every full working cut, as used in (4.5). -/
theorem full_cut_power_rank_upper {μ A B P κ cap : ℝ} (hμ : 0 < μ) (hA : 0 < A) (hB : 0 < B)
    (hAB : A ≤ B) (hAcap : A ≤ cap) (hcap : μ*B ≤ 1/2) (hP : 0 < P) (hPA : P ≤ A) (hκ : 0 ≤ κ)
    (h : List ℝ) (hcount : 1 ≤ countAbove h A) :
    cutPower (cappedStep μ B) P κ (fullCut A h) ≤ (4+2/(1-nu))*weightedCount h cap+κ^nu := by
  let C := fullCut A h
  have hgap : ∀ b ∈ C.unselected, b ≤ A := fun _ hb => fullCut_unselected hb
  have hs := cut_power_scaled_mass_bound hμ hA hB hcap hP hκ C (fun b hb => (hgap b hb).trans hAB)
  have hk := full_cut_gap_count_rank hA hAcap h hcount
  have hm := C.unselected_positiveMass_rank_bound hA hAcap (fun b hb _ => hgap b hb)
  have hword : C.word = h := cutSchedule_word _ _
  rw [hword] at hm
  have hp0 := Real.rpow_pos_of_pos hA nu
  have hp1 := Real.rpow_pos_of_pos hA (nu-1)
  have hcount0 : 0 ≤ (C.phases.length : ℝ)+1 := by positivity
  have hkp := mul_le_mul_of_nonneg_right hPA hcount0
  have hpad := mul_le_mul_of_nonneg_right hkp hp1.le
  have hmass := mul_le_mul_of_nonneg_right hm (show 0 ≤ 2*A^(nu-1) by positivity)
  have hselected := mul_le_mul_of_nonneg_right hk hp0.le
  have hcancel : A^(-nu)*A^nu = 1 := by rw [← Real.rpow_add hA,neg_add_cancel,Real.rpow_zero]
  have hmasscancel : A^(1-nu)*A^(nu-1) = 1 := by rw [← Real.rpow_add hA,show 1-nu+(nu-1) = (0 : ℝ) by ring,Real.rpow_zero]
  have hAprod : A*A^(nu-1) = A^nu := by
    calc
      _ = A^(1 : ℝ)*A^(nu-1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hA]; congr 1; ring
  have hselected' : ((C.phases.length : ℝ)+1)*A^nu ≤ 2*weightedCount h cap := by
    calc
      _ ≤ 2*weightedCount h cap*(A^(-nu)*A^nu) := by linear_combination hselected
      _ = _ := by rw [hcancel,mul_one]
  have hmass' : 2*Scalar.SignedIntervals.positiveMass C.unselected*A^(nu-1) ≤ (2/(1-nu))*weightedCount h cap := by
    calc
      _ ≤ (2/(1-nu))*weightedCount h cap*(A^(1-nu)*A^(nu-1)) := by linear_combination hmass
      _ = _ := by rw [hmasscancel,mul_one]
  have hpad' : ((C.phases.length : ℝ)+1)*P*A^(nu-1) ≤ 2*weightedCount h cap := by
    calc
      _ ≤ ((C.phases.length : ℝ)+1)*(A*A^(nu-1)) := by linear_combination hpad
      _ = _ := by rw [hAprod]
      _ ≤ _ := hselected'
  linear_combination hs+hselected'+hmass'+hpad'

end
end StrongSilver
