-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.StableCutLogBounds
import StrongSilver.CutPowerPadding

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

/-- A cut in a compressed tracked schedule still charges selected-step
conversion to the original schedule, through its exact sublist witness. -/
theorem stable_compressed_cut_log {κ μ B P loss : ℝ} (hμ : 0 < μ) (hB : 0 < B)
    (hcap : μ*B ≤ 1/2) (hP : 0 < P) (C : ScheduleCut) (h : List ℝ) (hsub : C.word.Sublist h)
    (hpiv : ∀ q ∈ C.phases, 2*P ≤ q.pivot) (hgap : ∀ q ∈ C.phases, ∀ b ∈ q.gap, b ≤ B)
    (hlower : ENNReal.ofReal (Real.exp (-loss)*(cutReferenceProduct μ P C.phases)^2) ≤ D κ h)
    (hD : D κ h ≤ 1) : -loss/2-4*μ*clippedMass h B ≤ cappedPhaseLogSum μ B P C.phases := by
  obtain ⟨hf,hprod⟩ := raw_reference_factors_positive hμ hcap hP C.phases hpiv hgap
  have hs := stable_exponential_product_log hprod hlower hD
  rw [log_cutReferenceProduct C.phases hf] at hs
  have hc := capped_reference_log_lower hμ hB hcap hP C.phases hpiv hgap
  have hm := C.selected_min_le_clippedMass hB.le (fun q hq => by have hh := hpiv q hq; linarith only [hh,hP])
  have hword : clippedMass C.word B ≤ clippedMass h B :=
    list_weight_sublist_le (fun b => max 0 (min b B)) (fun _ => le_max_left _ _) hsub
  have hscale := mul_le_mul_of_nonneg_left (hm.trans hword) (show 0 ≤ 4*μ by positivity)
  nlinarith only [hs,hc,hscale]

theorem cutLogProduct_empty_terminal {μ B P : ℝ} (C : ScheduleCut) (ht : C.terminal = []) :
    cutLogProduct (cappedStep μ B) P 0 C-Real.log P = cappedPhaseLogSum μ B P C.phases := by
  rw [cutLogProduct_capped_split,ht]
  simp only [gapPrefix,List.map_nil,Scalar.SignedIntervals.prefixMax,zero_add,add_zero,add_sub_cancel_right]

theorem cutPower_empty_terminal (φ : ℝ → ℝ) (P : ℝ) (C : ScheduleCut) (ht : C.terminal = []) :
    cutPower φ P 0 C-P^nu = (C.phases.map fun q => (gapPrefix φ q.gap+P)^nu).sum := by
  rw [cutPower_eq_phase_sum,ht]
  simp only [gapPrefix,List.map_nil,Scalar.SignedIntervals.prefixMax,zero_add,add_zero,add_sub_cancel_right]

end
end StrongSilver
