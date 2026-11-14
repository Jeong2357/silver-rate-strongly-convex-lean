-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AlternatingReplacement
import StrongSilver.WorkingCutReplacementBound

namespace StrongSilver.CompleteCutAssembly
open Real Filter
noncomputable section
set_option maxHeartbeats 4800000

/-- Candidate pairs after the original reservation, with multiplicity. -/
def ordinaryPairs (t : List ℝ) : CompleteCutAssembly → List (CutPhase × CutPhase)
  | .scalar _ => []
  | .positive s => (s.erase t).adjacentOrdinaryPairs
  | .leadingBlock _ _ s => (s.erase t).adjacentOrdinaryPairs
  | .leadingEnd _ _ => []

def alternatingPairGain (t : List ℝ) (f : CutPhase × CutPhase → ℝ) (reset : Bool) : CompleteCutAssembly → ℝ
  | .scalar _ => 0
  | .positive s => (((s.erase t).alternatingPairs reset reset).map f).sum
  | .leadingBlock _ _ s => (((s.erase t).alternatingPairs reset reset).map f).sum
  | .leadingEnd _ _ => 0

theorem pair_gain_partition (t : List ℝ) (f : CutPhase × CutPhase → ℝ) (s : CompleteCutAssembly) :
    s.alternatingPairGain t f true+s.alternatingPairGain t f false = ((s.ordinaryPairs t).map f).sum := by
  cases s with
  | scalar I => simp [alternatingPairGain,ordinaryPairs]
  | leadingEnd I c => simp [alternatingPairGain,ordinaryPairs]
  | positive s => exact (s.erase t).alternating_pair_sum f true
  | leadingBlock I c s => exact (s.erase t).alternating_pair_sum f true

/-- The pair providers determine a matching on the actual retained
suffix for each alternating choice, without changing reserved blocks. -/
theorem eventually_alternating_pair_witness : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ s : CompleteCutAssembly, ∀ t : List ℝ,
    s.PhaseValid A μ T P t → ∀ f : CutPhase × CutPhase → ℝ,
    (∀ p ∈ s.ordinaryPairs t, PairTraceExtension A μ P p (f p)) → ∀ reset : Bool,
    s.ReplacementWitness A μ P t (s.alternatingPairGain t f reset) := by
  filter_upwards [eventually_ordinary_phase_extension,eventually_matching_witness] with A hordinary hrealize
  intro μ T P s t hs f hf reset
  have hord : ∀ q : CutPhase, OrdinaryPhaseParameters A μ q.pivot T P q.gap →
      WordTraceExtension A μ q.word ((ordinaryReferenceFactor A μ q.pivot P q.gap)^2) := by
    intro q W
    exact hordinary μ T P q W
  apply hrealize μ T P s t _ hs
  cases s with
  | scalar I => exact le_rfl
  | leadingEnd I c => exact le_rfl
  | positive s => exact (s.erase t).alternating_replacement_plan hord f reset reset hs hf
  | leadingBlock I c s => exact (s.erase t).alternating_replacement_plan hord f reset reset hs hf

end
end StrongSilver.CompleteCutAssembly

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 4800000

/-- Exact finite full-cut pair test. One reservation is selected before
requesting any pair improvement. The two disjoint matchings control the
sum over all available adjacent pairs by the original full-cut loss. -/
theorem eventually_working_cut_pair_test : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P σ τ : ℝ, ∀ C : ScheduleCut,
    1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ ≤ 2/κ → μ*A ≤ 1/2 → 1 ≤ P →
    0 ≤ σ → σ ≤ 1 → 0 ≤ τ → τ ≤ 1 →
    (∀ q ∈ C.phases, P < q.pivot) →
    (∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ A) →
    (∀ b ∈ C.terminal, 0 < b → b ≤ A) → (∀ b ∈ C.word, 1-μ*b ≠ 0) →
    D κ C.word ≤ 1 →
    ∃ s : CompleteCutAssembly, s.phases = C.phases ∧
      s.WellFormed (ordinaryPhaseGood A μ T P) ∧ s.Counted (ordinaryPhaseGood A μ T P) ∧
      s.reserved.length ≤ 4*badPhaseCount (ordinaryPhaseGood A μ T P) C.phases ∧
      ∀ f : CutPhase × CutPhase → ℝ,
      (∀ p ∈ s.ordinaryPairs C.terminal, PairTraceExtension A μ P p (f p)) →
      2*(C.phases.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum+
        (((s.ordinaryPairs C.terminal).map f).sum)/2 ≤ workingCutLoss A κ μ T P σ τ C := by
  classical
  filter_upwards [eventually_working_cut_replacement_bound,CompleteCutAssembly.eventually_phaseValid,
    CompleteCutAssembly.eventually_alternating_pair_witness] with A hbound hvalid hmatch
  intro κ μ T P σ τ C hκ hμ hμ1 hμu hcap hP hσ hσ1 hτ hτ1 hpiv hgap ht hcrit hD
  obtain ⟨s,hph,hs,hcounted,hcount,hgain⟩ := hbound κ μ T P σ τ C hκ hμ hμ1 hμu hcap hP hσ hσ1 hτ hτ1 hpiv hgap ht hcrit
  have hword : s.word C.terminal = C.word := by simp only [CompleteCutAssembly.word,hph,ScheduleCut.word]
  have hv := hvalid μ T P (ordinaryPhaseGood A μ T P)
    (fun q hq => of_decide_eq_true hq) s hs C.terminal ht (by simpa only [hword] using hcrit)
  refine ⟨s,hph,hs,hcounted,hcount,?_⟩
  intro f hf
  have htrue := hgain _ (hmatch μ T P s C.terminal hv f hf true) hD
  have hfalse := hgain _ (hmatch μ T P s C.terminal hv f hf false) hD
  have hsum := s.pair_gain_partition C.terminal f
  linarith only [htrue,hfalse,hsum]

end
end StrongSilver
