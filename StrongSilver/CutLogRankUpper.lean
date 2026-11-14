-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutLogScaleUpper
import StrongSilver.PositivePartCut
import StrongSilver.FullCutPaddingRank

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

theorem cut_prefix_sum_mass_bound (φ : ℝ → ℝ) (C : ScheduleCut)
    (hp : ∀ q ∈ C.phases, gapPrefix φ q.gap ≤ 2*positiveMass q.gap)
    (ht : gapPrefix φ C.terminal ≤ 2*positiveMass C.terminal) :
    (C.phases.map fun q => gapPrefix φ q.gap).sum+gapPrefix φ C.terminal ≤ 2*positiveMass C.unselected := by
  have hs := List.sum_le_sum hp
  rw [List.sum_map_mul_left] at hs
  have hm := C.unselected_positiveMass
  nlinarith only [hs,ht,hm]

/-- Rank upper bound in (4.5), valid both for signed-prefix masses and
for the positive-sum masses L^S. -/
theorem full_cut_log_rank_upper_of_prefix_bound (φ : ℝ → ℝ) {A B P κ cap : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hAcap : A ≤ cap) (hP : 0 < P) (hPA : P ≤ A/2) (hAκ : A ≤ κ)
    (hφ : ∀ b, 0 < b → b ≤ φ b)
    (hprefix : ∀ g : List ℝ, (∀ b ∈ g, b ≤ B) → gapPrefix φ g ≤ 2*positiveMass g)
    (h : List ℝ) (hcount : 1 ≤ countAbove h A) :
    cutLogProduct φ P κ (fullCut A h)-Real.log κ ≤
      (4/(1-nu)+4)*weightedCount h cap*A^(-nu) := by
  let C := fullCut A h
  have hgap : ∀ b ∈ C.unselected, b ≤ A := fun b hb => fullCut_unselected hb
  have hp : ∀ q ∈ C.phases, gapPrefix φ q.gap ≤ 2*positiveMass q.gap := fun q hq =>
    hprefix q.gap (fun b hb => (hgap b (ScheduleCut.mem_gap_unselected hq hb)).trans hAB)
  have ht := hprefix C.terminal (fun b hb => (hgap b (ScheduleCut.mem_terminal_unselected hb)).trans hAB)
  have hmass := cut_prefix_sum_mass_bound φ C hp ht
  have hselected : ∀ q ∈ C.phases, A/2 ≤ φ q.pivot-P := by
    intro q hq
    have hpiv := fullCut_pivot hq
    have htrans := hφ q.pivot (hA.trans hpiv)
    linarith only [hpiv,htrans,hPA]
  have hlog := cut_log_scaled_mass_upper φ hA hP hAκ C hselected
  have hk := full_cut_gap_count_rank hA hAcap h hcount
  have hm := C.unselected_positiveMass_rank_bound hA hAcap (fun b hb _ => hgap b hb)
  have hword : C.word = h := cutSchedule_word _ _
  rw [hword] at hm
  have hpow : A^(1-nu)/A = A^(-nu) := by
    calc
      _ = A^(1-nu)/A^(1:ℝ) := by rw [Real.rpow_one]
      _ = A^((1-nu)-1) := (Real.rpow_sub hA _ _).symm
      _ = _ := by congr 1; ring
  have hmA : positiveMass C.unselected/A ≤ weightedCount h cap*A^(-nu)/(1-nu) := by
    have hh := div_le_div_of_nonneg_right hm hA.le
    have he : (weightedCount h cap*A^(1-nu)/(1-nu))/A = weightedCount h cap*A^(-nu)/(1-nu) := by
      calc
        _ = (weightedCount h cap/(1-nu))*(A^(1-nu)/A) := by ring
        _ = _ := by rw [hpow]; ring
    simpa only [he] using hh
  have hpad : (((C.phases.length:ℝ)+1)*P)/A ≤ (C.phases.length:ℝ)+1 := by
    apply (div_le_iff₀ hA).mpr
    have hh := mul_le_mul_of_nonneg_left (show P ≤ A by linarith only [hPA,hA])
      (show 0 ≤ (C.phases.length:ℝ)+1 by positivity)
    exact hh
  calc
    _ ≤ (2/A)*((C.phases.map fun q => gapPrefix φ q.gap).sum+gapPrefix φ C.terminal+
        ((C.phases.length:ℝ)+1)*P) := hlog
    _ ≤ (2/A)*(2*positiveMass C.unselected+((C.phases.length:ℝ)+1)*P) :=
      mul_le_mul_of_nonneg_left (add_le_add hmass le_rfl) (div_nonneg (by norm_num) hA.le)
    _ = 4*(positiveMass C.unselected/A)+2*((((C.phases.length:ℝ)+1)*P)/A) := by ring
    _ ≤ 4*(weightedCount h cap*A^(-nu)/(1-nu))+2*((C.phases.length:ℝ)+1) :=
      add_le_add (mul_le_mul_of_nonneg_left hmA (by norm_num)) (mul_le_mul_of_nonneg_left hpad (by norm_num))
    _ ≤ 4*(weightedCount h cap*A^(-nu)/(1-nu))+4*weightedCount h cap*A^(-nu) := by
      nlinarith only [hk]
    _ = _ := by ring

/-- The positive-sum full-cut logarithmic observable has the O(W A^-nu)
upper bound required by the cutoff integration arguments. -/
theorem full_cut_positive_sum_log_rank_upper {μ A B P κ cap : ℝ} (hμ : 0 < μ) (hA : 0 < A) (hB : 0 < B)
    (hAB : A ≤ B) (hAcap : A ≤ cap) (hcap : μ*B ≤ 1/2) (hP : 0 < P) (hPA : P ≤ A/2) (hAκ : A ≤ κ)
    (h : List ℝ) (hcount : 1 ≤ countAbove h A) :
    cutLogProduct (positivePartStep (cappedStep μ B)) P κ (fullCut A h)-Real.log κ ≤
      (4/(1-nu)+4)*weightedCount h cap*A^(-nu) := by
  have hcap1 : μ*B < 1 := by linarith only [hcap]
  apply full_cut_log_rank_upper_of_prefix_bound _ hA hAB hAcap hP hPA hAκ
    (fun b hb => (cappedStep_ge hμ hcap1 b).trans (le_max_left _ _))
    (fun g hg => positivePart_capped_gapPrefix_le_mass hμ hB hcap g hg) h hcount

end
end StrongSilver
