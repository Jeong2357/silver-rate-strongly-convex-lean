-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.DisjointPairCandidates

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 4800000

/-- Actual two-phase extension with its guaranteed logarithmic gain. -/
def PairTraceExtension (A μ P : ℝ) (pair : CutPhase × CutPhase) (gain : ℝ) : Prop :=
  WordTraceExtension A μ (pair.1.word++pair.2.word)
    (((ordinaryReferenceFactor A μ pair.1.pivot P pair.1.gap)^2*
      (ordinaryReferenceFactor A μ pair.2.pivot P pair.2.gap)^2)*Real.exp gain)

namespace WorkingAssembly

/-- Every alternating matching of available local pair constructions
produces a disjoint replacement plan on the full original assembly. -/
theorem alternating_replacement_plan {A μ T P : ℝ}
    (hordinary : ∀ q : CutPhase, OrdinaryPhaseParameters A μ q.pivot T P q.gap →
      WordTraceExtension A μ q.word ((ordinaryReferenceFactor A μ q.pivot P q.gap)^2))
    (f : CutPhase × CutPhase → ℝ) (reset take : Bool) (s : WorkingAssembly)
    (hs : s.Valid A μ T P)
    (hpairs : ∀ p ∈ s.adjacentOrdinaryPairs, PairTraceExtension A μ P p (f p)) :
    DisjointReplacementPlan A μ P s (((s.alternatingPairs reset take).map f).sum) := by
  cases s with
  | ordinaryEnd q t =>
    have hext := hordinary q hs.1
    have hh := DisjointReplacementPlan.ordinaryEnd (A := A) (μ := μ) (P := P) q t 0 (by
      simpa only [Real.exp_zero,mul_one] using hext)
    cases take <;> simpa only [alternatingPairs,List.map_nil,List.sum_nil] using hh
  | ordinary q s =>
    have hext := hordinary q hs.1
    have htail : ∀ p ∈ s.adjacentOrdinaryPairs, PairTraceExtension A μ P p (f p) :=
      fun p hp => hpairs p ((adjacentPairs_tail q s).subset hp)
    cases take with
    | false =>
      have ht := alternating_replacement_plan hordinary f reset true s hs.2 htail
      have hh := DisjointReplacementPlan.ordinary q s _ 0 ht (by
        simpa only [Real.exp_zero,mul_one] using hext)
      simpa only [alternatingPairs_false,add_zero] using hh
    | true =>
      cases s with
      | ordinaryEnd r t =>
        have he := hpairs (q,r) (by simp [adjacentOrdinaryPairs])
        have hh := DisjointReplacementPlan.pairEnd q r t (f (q,r)) he
        simpa only [alternatingPairs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using hh
      | ordinary r s =>
        have ht := alternating_replacement_plan hordinary f reset true s hs.2.2
          (fun p hp => htail p ((adjacentPairs_tail r s).subset hp))
        have he := hpairs (q,r) (by simp [adjacentOrdinaryPairs])
        have hh := DisjointReplacementPlan.pair q r s _ (f (q,r)) ht he
        simpa only [alternatingPairs,List.map_cons,List.sum_cons,add_comm] using hh
      | block r I c s =>
        have ht := alternating_replacement_plan hordinary f reset true (.block r I c s) hs.2 htail
        have hh := DisjointReplacementPlan.ordinary q (.block r I c s) _ 0 ht (by
          simpa only [Real.exp_zero,mul_one] using hext)
        simpa only [alternatingPairs,add_zero] using hh
      | blockEnd r I c t =>
        have ht := DisjointReplacementPlan.blockEnd (A := A) (μ := μ) (P := P) r I c t
        have hh := DisjointReplacementPlan.ordinary q (.blockEnd r I c t) 0 0 ht (by
          simpa only [Real.exp_zero,mul_one] using hext)
        simpa only [alternatingPairs,List.map_nil,List.sum_nil,add_zero] using hh
      | noConnector r I t =>
        have ht := DisjointReplacementPlan.noConnector (A := A) (μ := μ) (P := P) r I t
        have hh := DisjointReplacementPlan.ordinary q (.noConnector r I t) 0 0 ht (by
          simpa only [Real.exp_zero,mul_one] using hext)
        simpa only [alternatingPairs,List.map_nil,List.sum_nil,add_zero] using hh
  | block q I c s =>
    have ht := alternating_replacement_plan hordinary f reset reset s hs.2.2.2.2.2 hpairs
    exact DisjointReplacementPlan.block q I c s _ ht
  | blockEnd q I c t =>
    have hh := DisjointReplacementPlan.blockEnd (A := A) (μ := μ) (P := P) q I c t
    cases take <;> simpa only [alternatingPairs,List.map_nil,List.sum_nil] using hh
  | noConnector q I t =>
    have hh := DisjointReplacementPlan.noConnector (A := A) (μ := μ) (P := P) q I t
    cases take <;> simpa only [alternatingPairs,List.map_nil,List.sum_nil] using hh
termination_by sizeOf s

end WorkingAssembly
end
end StrongSilver
