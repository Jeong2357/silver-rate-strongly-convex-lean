-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialFixedAssemblyBound
import StrongSilver.TrackedAssemblyProperties
import StrongSilver.CompressedCutLog

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2800000

theorem refinePhases_word (choose : ℕ → ℝ → Bool) (qs : List CutPhase) :
    (qs.flatMap (refinePhase choose)).flatMap CutPhase.word = qs.flatMap CutPhase.word := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp only [List.flatMap_cons,List.flatMap_append,refinePhase_word,ih]

def initialStableLogRemainder (κ B μ : ℝ) (good : CutPhase → Bool) (s : CompleteInitialCutAssembly)
    (t : List ℝ) : ℝ :=
  3*μ*(phaseGapMass s.phases+Scalar.SignedIntervals.positiveMass t)+
    (7*(initialLogPriceConstant+6)/2)*(badPhaseCount good s.phases : ℝ)*(1+Real.log (κ/B))+
    largeInverseCharge κ (s.word t) μ+4*μ*clippedMass (s.word t) B

/-- Uniform tracked-only logarithmic lower bound from actual initial-cut
trajectories. One assembly and curvature can be fixed before every cutoff
and tie choice occurring in the refinement. -/
theorem eventually_initial_stable_refined_log : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → InitialPhaseBudget B μ q.pivot T κ B q.gap) →
      ∀ s : CompleteInitialCutAssembly, s.WellFormed good → s.Counted good →
      ∀ choose : ℕ → ℝ → Bool, ∀ t : List ℝ,
      A ≤ B → 2 ≤ B → B ≤ κ → κ ≤ A^((1003 : ℝ)/1000) → 1 ≤ κ →
      1/κ ≤ μ → μ ≤ 9/(8*κ) → μ*B ≤ 1/2 →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ i b, choose i b = true → A ≤ b) → (∀ i b, choose i b = false → 0 < b → b ≤ A) →
      (∀ q ∈ s.phases, ∀ b ∈ q.gap, 0 < b → b ≤ B) →
      (∀ b ∈ t, 0 < b → b ≤ B) → (∀ b ∈ s.word t, 1-μ*b ≠ 0) → D κ (s.word t) ≤ 1 →
      -1200*((s.trackedPhases.flatMap (refinePhase choose)).length : ℝ)/Real.log A-
        initialStableLogRemainder κ B μ good s t ≤ cappedPhaseLogSum μ B P (s.trackedPhases.flatMap (refinePhase choose)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_fixed_initial_assembly_bound,
    eventually_initial_refined_parameters,eventually_const_mul_power_le (by norm_num : (199 : ℝ)/200 < 499/500) 2]
    with A hA hactual hparams hmargin
  intro κ B μ T P good hW s hs hc choose t hAB hB hBκ hκA hκ hμ hμu hcap hPL hPU hselected hunselected hgap ht hcrit hD
  have hA0 := zero_lt_one.trans hA
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hμ0 : 0 < μ := (one_div_pos.mpr (zero_lt_one.trans_le hκ)).trans_le hμ
  have hP : 0 < P := (Real.rpow_pos_of_pos hA0 _).trans_le hPL
  let qs := s.trackedPhases.flatMap (refinePhase choose)
  let C : ScheduleCut := ⟨qs,[]⟩
  have hOrd : ∀ q ∈ qs, OrdinaryPhaseParameters A μ q.pivot T P q.gap := by
    intro q hq
    obtain ⟨z,hz,hq⟩ := List.mem_flatMap.mp hq
    exact hparams κ B μ T P z choose hAB hκA hPL hPU (hW z (s.tracked_good hs z hz)) hselected hunselected q hq
  have hpiv : ∀ q ∈ C.phases, 2*P ≤ q.pivot := by
    intro q hq
    have W := hOrd q hq
    have hh := mul_le_mul_of_nonneg_left hPU (by norm_num : (0 : ℝ) ≤ 2)
    exact hh.trans (hmargin.trans W.pivot_lower)
  have hgaps : ∀ q ∈ C.phases, ∀ b ∈ q.gap, b ≤ B := by
    intro q hq b hb
    by_cases hb0 : 0 < b
    · exact ((hOrd q hq).gap_cap b hb hb0).trans hAB
    · exact (le_of_not_gt hb0).trans hB0.le
  have hword : C.word = s.trackedPhases.flatMap CutPhase.word := by
    change (s.trackedPhases.flatMap (refinePhase choose)).flatMap CutPhase.word++[] = _
    rw [List.append_nil,refinePhases_word]
  have hsub : C.word.Sublist (s.word t) := by
    rw [hword]
    exact (s.trackedPhases_sublist.flatMap CutPhase.word).trans (List.sublist_append_left _ _)
  have hlower := hactual κ B μ T P good hW s hs hc choose t hAB hB hBκ hκA hκ hμ hμu hcap hPL hPU
    hselected hunselected hgap ht hcrit
  have hlog := stable_compressed_cut_log hμ0 hB0 hcap hP C (s.word t) hsub hpiv hgaps hlower hD
  unfold initialStableLogRemainder initialCutLoss at *
  linear_combination hlog

end
end StrongSilver
