-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReferenceLogConversion
import StrongSilver.ScheduleCutSublist

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

theorem raw_reference_factors_positive {μ B P : ℝ} (hμ : 0 < μ) (hcap : μ*B ≤ 1/2) (hP : 0 < P)
    (qs : List CutPhase) (hpiv : ∀ q ∈ qs, 2*P ≤ q.pivot) (hgap : ∀ q ∈ qs, ∀ b ∈ q.gap, b ≤ B) :
    (∀ q ∈ qs, 0 < (q.pivot-P)/(transformedGapMaximum μ q.gap+P)) ∧ 0 < cutReferenceProduct μ P qs := by
  have hf : ∀ q ∈ qs, 0 < (q.pivot-P)/(transformedGapMaximum μ q.gap+P) := by
    intro q hq
    have hm := transformedGapMaximum_nonnegative hμ q.gap (fun b hb =>
      (mul_le_mul_of_nonneg_left (hgap q hq b hb) hμ.le).trans_lt (by linarith only [hcap] : μ*B < 1))
    have hp := hpiv q hq
    exact div_pos (by linarith only [hp,hP]) (add_pos_of_nonneg_of_pos hm hP)
  refine ⟨hf,?_⟩
  apply List.prod_pos
  intro x hx
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
  exact hf q hq

theorem stable_full_capped_cut_log {κ μ B P loss : ℝ} (hκ : 0 < κ) (hμ : 0 < μ) (hB : 0 < B)
    (hcap : μ*B ≤ 1/2) (hP : 0 < P) (C : ScheduleCut)
    (hpiv : ∀ q ∈ C.phases, 2*P ≤ q.pivot) (hgap : ∀ q ∈ C.phases, ∀ b ∈ q.gap, b ≤ B)
    (hlower : ENNReal.ofReal (Real.exp (-loss)*(cutReferenceProduct μ P C.phases)^2) ≤ D κ C.word)
    (hD : D κ C.word ≤ 1) :
    -loss/2-4*μ*clippedMass C.word B ≤ cutLogProduct (cappedStep μ B) P κ C-Real.log κ := by
  obtain ⟨hf,hprod⟩ := raw_reference_factors_positive hμ hcap hP C.phases hpiv hgap
  have hs := stable_exponential_product_log hprod hlower hD
  rw [log_cutReferenceProduct C.phases hf] at hs
  have hc := full_cut_capped_log_lower hκ hμ hB hcap hP C hpiv hgap
  linarith only [hs,hc]

theorem ScheduleCut.subphase_min_le_clippedMass {B : ℝ} (hB : 0 ≤ B) (C : ScheduleCut) (qs : List CutPhase)
    (hs : qs.Sublist C.phases) (hpiv : ∀ q ∈ qs, 0 ≤ q.pivot) :
    (qs.map fun q => min q.pivot B).sum ≤ clippedMass C.word B := by
  let w : ℝ → ℝ := fun b => max 0 (min b B)
  have hsub := list_weight_sublist_le (fun q : CutPhase => w q.pivot) (fun q => le_max_left 0 (min q.pivot B)) hs
  have hwhole := C.selected_weight_le w (fun b => le_max_left 0 (min b B))
  have hm : qs.map (fun q => w q.pivot) = qs.map (fun q => min q.pivot B) := by
    apply List.map_congr_left
    intro q hq
    exact max_eq_right (le_min (hpiv q hq) hB)
  rw [hm] at hsub
  exact hsub.trans hwhole

/-- The same conversion applies to the tracked factors: the sublist proof
prevents any selected step from being charged more than once. -/
theorem stable_subphase_capped_cut_log {κ μ B P loss : ℝ} (hμ : 0 < μ) (hB : 0 < B)
    (hcap : μ*B ≤ 1/2) (hP : 0 < P) (C : ScheduleCut) (qs : List CutPhase)
    (hsub : qs.Sublist C.phases) (hpiv : ∀ q ∈ qs, 2*P ≤ q.pivot) (hgap : ∀ q ∈ qs, ∀ b ∈ q.gap, b ≤ B)
    (hlower : ENNReal.ofReal (Real.exp (-loss)*(cutReferenceProduct μ P qs)^2) ≤ D κ C.word)
    (hD : D κ C.word ≤ 1) : -loss/2-4*μ*clippedMass C.word B ≤ cappedPhaseLogSum μ B P qs := by
  obtain ⟨hf,hprod⟩ := raw_reference_factors_positive hμ hcap hP qs hpiv hgap
  have hs := stable_exponential_product_log hprod hlower hD
  rw [log_cutReferenceProduct qs hf] at hs
  have hc := capped_reference_log_lower hμ hB hcap hP qs hpiv hgap
  have hm := C.subphase_min_le_clippedMass hB.le qs hsub (fun q hq => by have hp := hpiv q hq; linarith only [hp,hP])
  have hscale := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4*μ by positivity)
  nlinarith only [hs,hc,hscale]

end
end StrongSilver
