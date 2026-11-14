-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutAssembly
import StrongSilver.WorkingAssemblyLog

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2200000

theorem eventually_ordinary_connector_bounds : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      2 ≤ b ∧ b ≤ A^(2 : ℝ) ∧ 1/32 ≤ 1-μ*b := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 499/500)).eventually (eventually_ge_atTop (2 : ℝ))]
    with A hA hlarge
  intro μ b T P h W
  have hmul := mul_le_mul_of_nonneg_left W.b_lt_T.le W.mu_positive.le
  exact ⟨hlarge.trans W.pivot_lower,
    W.pivot_upper.trans (Real.rpow_le_rpow_of_exponent_le hA (by norm_num)),
    by linarith only [hmul,W.curvature]⟩

namespace CutAssembly

theorem eventually_valid_erase : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      ∀ s : CutAssembly, s.WellFormed good → ∀ t : List ℝ,
      (∀ a ∈ t, 0 < a → a ≤ A) → (∀ a ∈ (s.erase t).word, 1-μ*a ≠ 0) →
      (s.erase t).Valid A μ T P := by
  filter_upwards [eventually_ordinary_connector_bounds] with A hconn
  intro μ T P good hW s
  induction s with
  | ordinaryEnd q =>
    intro hq t ht _
    exact ⟨hW q hq,ht⟩
  | ordinary q s ih =>
    intro ⟨hq,hs⟩ t ht hcritical
    refine ⟨hW q hq,ih hs t ht ?_⟩
    intro a ha
    exact hcritical a (List.mem_append_right _ ha)
  | block q I c s ih =>
    intro ⟨hq,hc,hs⟩ t ht hcritical
    obtain ⟨hc2,hcA,hqc⟩ := hconn μ c.pivot T P c.gap (hW c hc)
    refine ⟨hW q hq,hc2,hcA,hqc,?_,ih hs t ht ?_⟩
    · intro a ha
      exact hcritical a (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ ha)))
    · intro a ha
      exact hcritical a (List.mem_append_right _ (List.mem_append_right _ ha))
  | blockEnd q I c =>
    intro ⟨hq,hc⟩ t ht hcritical
    obtain ⟨hc2,_,hqc⟩ := hconn μ c.pivot T P c.gap (hW c hc)
    refine ⟨hW q hq,hc2,hqc,?_,ht⟩
    intro a ha
    exact hcritical a (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ ha)))
  | noConnector q I =>
    intro hq t ht hcritical
    refine ⟨hW q hq,?_,ht⟩
    intro a ha
    exact hcritical a (List.mem_append_right _ (List.mem_append_left _ ha))

theorem eventually_realize : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      ∀ s : CutAssembly, s.WellFormed good → ∀ t : List ℝ,
      (∀ a ∈ t, 0 < a → a ≤ A) → (∀ a ∈ s.phases.flatMap CutPhase.word++t, 1-μ*a ≠ 0) →
      Nonempty (PositiveTrace μ (s.phases.flatMap CutPhase.word++t) (workingGateFraction A)
        (A^(10 : ℝ)) (A^(10 : ℝ)) ((s.erase t).rate A μ P)) := by
  filter_upwards [eventually_valid_erase,WorkingAssembly.eventually_realize] with A hvalid hrealize
  intro μ T P good hW s hs t ht hcritical
  have hh : ∀ a ∈ (s.erase t).word, 1-μ*a ≠ 0 := by simpa only [s.erase_word] using hcritical
  simpa only [s.erase_word] using hrealize μ T P (s.erase t) (hvalid μ T P good hW s hs t ht hh)

end CutAssembly

/-- Every cut beginning with a good phase admits a complete backward
assembly, including all exceptional steps. No cut-realization assumption is used. -/
theorem eventually_cut_with_good_first_realizable : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      ∀ q : CutPhase, ∀ qs : List CutPhase, ∀ t : List ℝ,
      good q = true → (∀ a ∈ t, 0 < a → a ≤ A) →
      (∀ a ∈ (q::qs).flatMap CutPhase.word++t, 1-μ*a ≠ 0) →
      ∃ s : CutAssembly, s.phases = q::qs ∧ s.WellFormed good ∧
        Nonempty (PositiveTrace μ ((q::qs).flatMap CutPhase.word++t) (workingGateFraction A)
          (A^(10 : ℝ)) (A^(10 : ℝ)) ((s.erase t).rate A μ P)) := by
  filter_upwards [CutAssembly.eventually_realize] with A hrealize
  intro μ T P good hW q qs t hq ht hcritical
  obtain ⟨s,hph,hs⟩ := exists_cutAssembly good q qs hq
  refine ⟨s,hph,hs,?_⟩
  have hh : ∀ a ∈ s.phases.flatMap CutPhase.word++t, 1-μ*a ≠ 0 := by simpa only [hph] using hcritical
  simpa only [hph] using hrealize μ T P good hW s hs t ht hh

end
end StrongSilver
