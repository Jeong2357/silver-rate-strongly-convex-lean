-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutRankBudgets
import StrongSilver.CutPowerPadding
import Mathlib.Algebra.BigOperators.Ring.List

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2200000

theorem cappedStep_positive_upper {μ B b : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hcap : μ*B ≤ 1/2) (hb : b ≤ B) :
    max (cappedStep μ B b) 0 ≤ 2*max b 0 := by
  by_cases hb0 : 0 < b
  · have hd := (cappedStep_defect (b := b) hμ hcap).2
    rw [min_eq_left hb] at hd
    have hm := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hb hμ.le).trans hcap) hb0.le
    rw [max_eq_left hb0.le]
    exact max_le (by nlinarith only [hd,hm]) (by linarith only [hb0])
  · have hh := cappedStep_nonpos hμ hB.le (le_of_not_gt hb0)
    rw [max_eq_right hh,max_eq_right (le_of_not_gt hb0)]
    norm_num

theorem capped_gapPrefix_le_mass {μ B : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hcap : μ*B ≤ 1/2)
    (h : List ℝ) (hh : ∀ b ∈ h, b ≤ B) : gapPrefix (cappedStep μ B) h ≤ 2*Scalar.SignedIntervals.positiveMass h := by
  have hp := Scalar.SignedIntervals.prefixMax_le_positiveMass (h.map (cappedStep μ B))
  have hm : Scalar.SignedIntervals.positiveMass (h.map (cappedStep μ B)) ≤ 2*Scalar.SignedIntervals.positiveMass h := by
    change ((h.map (cappedStep μ B)).map fun b => max b 0).sum ≤ _
    rw [List.map_map]
    have hs := List.sum_le_sum (l := h) (f := fun b => max (cappedStep μ B b) 0) (g := fun b => 2*max b 0)
      (fun b hb => cappedStep_positive_upper hμ hB hcap (hh b hb))
    rw [List.sum_map_mul_left] at hs
    exact hs
  exact hp.trans hm

theorem clippedMass_le_length {A : ℝ} (hA : 0 ≤ A) (h : List ℝ) : clippedMass h A ≤ (h.length : ℝ)*A := by
  induction h with
  | nil => simp [clippedMass]
  | cons b h ih =>
    have hh : max 0 (min b A) ≤ A := max_le hA (min_le_right _ _)
    simp only [clippedMass,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
    nlinarith only [hh,ih]

theorem padded_prefix_power_linear {μ B : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hcap : μ*B ≤ 1/2)
    (h : List ℝ) (hh : ∀ b ∈ h, b ≤ B) :
    (gapPrefix (cappedStep μ B) h+1)^nu ≤ 2*Scalar.SignedIntervals.positiveMass h+1 := by
  have hm := capped_gapPrefix_le_mass hμ hB hcap h hh
  have hbase : 1 ≤ gapPrefix (cappedStep μ B) h+1 := by have hx := gapPrefix_nonnegative (cappedStep μ B) h; linarith only [hx]
  have hp := Real.rpow_le_rpow_of_exponent_le hbase nu_lt_one.le
  simp only [Real.rpow_one] at hp
  linarith only [hp,hm]

/-- A linear mass bound suffices for the final averaging scale because
nu is greater than one half. -/
theorem full_cut_power_crude_upper {κ μ A B : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hcap : μ*B ≤ 1/2)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hκ : 0 ≤ κ) (h : List ℝ) (hlen : 1 ≤ h.length) :
    cutPower (cappedStep μ B) 1 κ (fullCut A h) ≤ 4*(h.length : ℝ)*A+κ^nu := by
  let C := fullCut A h
  have hu : ∀ b ∈ C.unselected, b ≤ A := fun _ hb => fullCut_unselected hb
  have hg : ∀ q ∈ C.phases, ∀ b ∈ q.gap, b ≤ B :=
    fun q hq b hb => (hu b (ScheduleCut.mem_gap_unselected hq hb)).trans hAB
  have ht : ∀ b ∈ C.terminal, b ≤ B := fun b hb => (hu b (ScheduleCut.mem_terminal_unselected hb)).trans hAB
  have hs : (C.phases.map fun q => (gapPrefix (cappedStep μ B) q.gap+1)^nu).sum ≤
      2*(C.phases.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum+(C.phases.length : ℝ) := by
    have hh := List.sum_le_sum (l := C.phases) (f := fun q => (gapPrefix (cappedStep μ B) q.gap+1)^nu)
      (g := fun q => 2*Scalar.SignedIntervals.positiveMass q.gap+1)
      (fun q hq => padded_prefix_power_linear hμ hB hcap q.gap (hg q hq))
    simpa only [List.sum_map_add,List.sum_map_mul_left,List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one] using hh
  have hterm := padded_prefix_power_linear hμ hB hcap C.terminal ht
  have hmass := C.unselected_positiveMass
  have hU := C.unselected_positiveMass_le_clipped (zero_le_one.trans hA) (fun b hb _ => hu b hb)
  have hclip := clippedMass_le_length (zero_le_one.trans hA) h
  have hword : C.word = h := cutSchedule_word _ _
  rw [hword] at hU
  have hp : (C.phases.length : ℝ) ≤ (h.length : ℝ) := by
    have hh := C.length_partition
    rw [hword] at hh
    exact_mod_cast (show C.phases.length ≤ h.length by omega)
  have hlenR : (1 : ℝ) ≤ (h.length : ℝ) := by exact_mod_cast hlen
  have hAprod := mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg h.length : (0 : ℝ) ≤ (h.length : ℝ))
  have hzero : cutPower (cappedStep μ B) 1 0 C ≤ 4*(h.length : ℝ)*A := by
    rw [cutPower_eq_phase_sum]
    simp only [add_zero]
    nlinarith only [hs,hterm,hmass,hU,hclip,hp,hlenR,hAprod]
  have hreserve := cutPower_reserve_increment (cappedStep μ B) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0) hκ C
  simp only [zero_add] at hreserve
  exact hreserve.trans (add_le_add hzero le_rfl)

end
end StrongSilver
