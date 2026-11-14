-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialCutProduct

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

/-- The initial reservation and curvature may be fixed before varying A.
This uniform form is needed when summing many cuts in Lemma 3.9. -/
theorem eventually_fixed_initial_assembly_bound : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → InitialPhaseBudget B μ q.pivot T κ B q.gap) →
      ∀ s : CompleteInitialCutAssembly, s.WellFormed good → s.Counted good →
      ∀ choose : ℕ → ℝ → Bool, ∀ t : List ℝ,
      A ≤ B → 2 ≤ B → B ≤ κ → κ ≤ A^((1003 : ℝ)/1000) →
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 9/(8*κ) → μ*B ≤ 1/2 →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ i b, choose i b = true → A ≤ b) → (∀ i b, choose i b = false → 0 < b → b ≤ A) →
      (∀ q ∈ s.phases, ∀ b ∈ q.gap, 0 < b → b ≤ B) →
      (∀ b ∈ t, 0 < b → b ≤ B) → (∀ b ∈ s.word t, 1-μ*b ≠ 0) →
      ENNReal.ofReal (Real.exp (-initialCutLoss A κ B μ good s choose t)*
        (cutReferenceProduct μ P (s.trackedPhases.flatMap (refinePhase choose)))^2) ≤ D κ (s.word t) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),CompleteInitialCutAssembly.eventually_phaseValid,
    CompleteInitialCutAssembly.eventually_distance_lower,eventually_initial_refined_parameters]
    with A hA hvalid hlower hparams
  intro κ B μ T P good hW s hs hc choose t hAB hB hBκ hκA hκ hμ hμu hcap hPL hPU hselected hunselected hgap ht hcritical
  have hκ0 := zero_lt_one.trans_le hκ
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hμ1 : μ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hB hμ0.le
    nlinarith only [hh,hcap]
  have hv := hvalid κ B μ T P good hW s hs choose t hAB hB hκA hPL hPU hselected hunselected hcritical
  have hr := s.rate_positive (t := t) hA hκ0 hB0 hv
  have hlog := s.log_rate (t := t) hA hκ0 hB0 hv
  have hOrd : ∀ z ∈ s.trackedPhases.flatMap (refinePhase choose), OrdinaryPhaseParameters A μ z.pivot T P z.gap := by
    intro z hz
    obtain ⟨q,hq,hz⟩ := List.mem_flatMap.mp hz
    exact hparams κ B μ T P q choose hAB hκA hPL hPU (hW q (s.tracked_good hs q hq)) hselected hunselected z hz
  have hgaps : ∀ q ∈ s.reserved, ∀ b ∈ q.gap, 0 < b → b ≤ B :=
    fun q hq => hgap q (CompleteInitialCutAssembly.mem_reserved hq)
  have hcost := s.logCost_global_budget (zero_lt_one.trans hA) hκ0 hB0 ((one_le_div hB0).mpr hBκ)
    hμ hμu hcap good hs hc choose t hOrd hgaps
  change s.logCost A κ B μ P choose t ≤ initialCutLoss A κ B μ good s choose t at hcost
  rw [s.referenceLog_eq_sum μ P choose] at hlog
  have hlogLower : 2*((s.trackedPhases.flatMap (refinePhase choose)).map
      fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum-
      initialCutLoss A κ B μ good s choose t ≤ Real.log (s.rate A κ B μ P choose t) := by linarith only [hlog,hcost]
  have hprod := exp_two_log_sum (fun q : CutPhase => (q.pivot-P)/(transformedGapMaximum μ q.gap+P))
    (s.trackedPhases.flatMap (refinePhase choose)) (fun q hq => (hOrd q hq).padded_ratio_positive hA)
  have he := Real.exp_le_exp.mpr hlogLower
  rw [Real.exp_log hr,sub_eq_add_neg,Real.exp_add,hprod] at he
  have hrBound : Real.exp (-initialCutLoss A κ B μ good s choose t)*
      (cutReferenceProduct μ P (s.trackedPhases.flatMap (refinePhase choose)))^2 ≤ s.rate A κ B μ P choose t := by
    simpa only [cutReferenceProduct,mul_comm] using he
  exact (ENNReal.ofReal_le_ofReal hrBound).trans
    (hlower κ B μ T P good hW s hs choose t hAB hB hκA hκ hμ hμ1 hcap hPL hPU hselected hunselected ht hcritical)

end
end StrongSilver
