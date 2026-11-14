-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutMasses
import StrongSilver.WorkingCutBound
import StrongSilver.LayerCake

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2000000

def rawReferenceLog (μ P : ℝ) (qs : List CutPhase) : ℝ :=
  (qs.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum

def cappedPhaseLogSum (μ B P : ℝ) (qs : List CutPhase) : ℝ :=
  (qs.map fun q => Real.log (gapPrefix (cappedStep μ B) q.gap+P)).sum-
    (qs.map fun q => Real.log (cappedStep μ B q.pivot-P)).sum

theorem capped_phase_log_lower {μ B P : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hcap : μ*B ≤ 1/2) (hP : 0 < P)
    (q : CutPhase) (hpiv : 2*P ≤ q.pivot) (hgap : ∀ b ∈ q.gap, b ≤ B) :
    -Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))-4*μ*min q.pivot B ≤
      Real.log (gapPrefix (cappedStep μ B) q.gap+P)-Real.log (cappedStep μ B q.pivot-P) := by
  have hcap1 : μ*B < 1 := by linarith only [hcap]
  have hm := transformedGapMaximum_nonnegative hμ q.gap (fun b hb => (mul_le_mul_of_nonneg_left (hgap b hb) hμ.le).trans_lt hcap1)
  have hnum : 0 < q.pivot-P := by linarith only [hpiv,hP]
  have hden := add_pos_of_nonneg_of_pos hm hP
  have hφpos : 0 < cappedStep μ B q.pivot-P := by have hh := cappedStep_ge hμ hcap1 q.pivot; linarith only [hh,hnum]
  have hc := (selected_factor_conversion hμ hB hcap hP hpiv).2
  rw [Real.log_div hφpos.ne' hnum.ne'] at hc
  rw [capped_gapPrefix_eq hμ hcap1 q.gap hgap,Real.log_div hnum.ne' hden.ne']
  linarith only [hc]

theorem capped_reference_log_lower {μ B P : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hcap : μ*B ≤ 1/2) (hP : 0 < P)
    (qs : List CutPhase) (hpiv : ∀ q ∈ qs, 2*P ≤ q.pivot) (hgap : ∀ q ∈ qs, ∀ b ∈ q.gap, b ≤ B) :
    -rawReferenceLog μ P qs-4*μ*(qs.map fun q => min q.pivot B).sum ≤ cappedPhaseLogSum μ B P qs := by
  induction qs with
  | nil => simp [rawReferenceLog,cappedPhaseLogSum]
  | cons q qs ih =>
    have hh := capped_phase_log_lower hμ hB hcap hP q (hpiv q (by simp)) (hgap q (by simp))
    have ht := ih (fun z hz => hpiv z (List.mem_cons_of_mem q hz)) (fun z hz => hgap z (List.mem_cons_of_mem q hz))
    simp only [rawReferenceLog,cappedPhaseLogSum,List.map_cons,List.sum_cons] at ht ⊢
    nlinarith only [hh,ht]

theorem ScheduleCut.selected_min_le_clippedMass {B : ℝ} (hB : 0 ≤ B) (C : ScheduleCut)
    (hpiv : ∀ q ∈ C.phases, 0 ≤ q.pivot) :
    (C.phases.map fun q => min q.pivot B).sum ≤ clippedMass C.word B := by
  let w : ℝ → ℝ := fun b => max 0 (min b B)
  have hh := C.selected_weight_le w (fun _ => le_max_left _ _)
  have hm : C.phases.map (fun q => w q.pivot) = C.phases.map (fun q => min q.pivot B) := by
    apply List.map_congr_left
    intro q hq
    exact max_eq_right (le_min (hpiv q hq) hB)
  rw [hm] at hh
  exact hh

theorem cutLogProduct_capped_split (μ B P reserve : ℝ) (C : ScheduleCut) :
    cutLogProduct (cappedStep μ B) P reserve C = cappedPhaseLogSum μ B P C.phases+
      Real.log (gapPrefix (cappedStep μ B) C.terminal+P+reserve) := by
  simp only [cutLogProduct,cutMasses,cappedPhaseLogSum,List.map_append,List.sum_append,
    List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,List.map_map,Function.comp_def,add_zero]
  ring

theorem full_cut_capped_log_lower {κ μ B P : ℝ} (hκ : 0 < κ) (hμ : 0 < μ) (hB : 0 < B)
    (hcap : μ*B ≤ 1/2) (hP : 0 < P) (C : ScheduleCut)
    (hpiv : ∀ q ∈ C.phases, 2*P ≤ q.pivot) (hgap : ∀ q ∈ C.phases, ∀ b ∈ q.gap, b ≤ B) :
    -rawReferenceLog μ P C.phases-4*μ*clippedMass C.word B ≤
      cutLogProduct (cappedStep μ B) P κ C-Real.log κ := by
  have hh := capped_reference_log_lower hμ hB hcap hP C.phases hpiv hgap
  have hm := C.selected_min_le_clippedMass hB.le (fun q hq => by have hp := hpiv q hq; linarith only [hp,hP])
  have hscale := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4*μ by positivity)
  have hterm : Real.log κ ≤ Real.log (gapPrefix (cappedStep μ B) C.terminal+P+κ) := by
    apply Real.log_le_log hκ
    have hx := gapPrefix_nonnegative (cappedStep μ B) C.terminal
    linarith only [hx,hP]
  rw [cutLogProduct_capped_split]
  nlinarith only [hh,hscale,hterm]

theorem log_cutReferenceProduct {μ P : ℝ} (qs : List CutPhase)
    (hf : ∀ q ∈ qs, 0 < (q.pivot-P)/(transformedGapMaximum μ q.gap+P)) :
    Real.log (cutReferenceProduct μ P qs) = rawReferenceLog μ P qs := by
  have hh : ∀ x ∈ qs.map (fun q => (q.pivot-P)/(transformedGapMaximum μ q.gap+P)), 0 < x := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hf q hq
  rw [cutReferenceProduct,log_list_product _ hh]
  simp only [rawReferenceLog,List.map_map,Function.comp_def]

theorem stable_exponential_product_log {κ loss r : ℝ} {h : List ℝ} (hr : 0 < r)
    (hlower : ENNReal.ofReal (Real.exp (-loss)*r^2) ≤ D κ h) (hD : D κ h ≤ 1) : 2*Real.log r ≤ loss := by
  have hpos : 0 < Real.exp (-loss)*r^2 := mul_pos (Real.exp_pos _) (sq_pos_of_pos hr)
  have hh := ENNReal.toReal_mono ENNReal.one_ne_top (hlower.trans hD)
  simp only [ENNReal.toReal_ofReal hpos.le,ENNReal.toReal_one] at hh
  have hlog := Real.log_le_log hpos hh
  rw [Real.log_one,Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero 2 hr.ne'),Real.log_exp,Real.log_pow] at hlog
  norm_num at hlog
  linarith only [hlog]

end
end StrongSilver
