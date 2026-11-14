-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingTraceOrdinary
import StrongSilver.TraceExceptional
import StrongSilver.TraceTerminalBases
import StrongSilver.ScheduleCut

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

/-- Backward assembly operations. A block word contains the actual steps,
including the gaps of reserved phases. -/
inductive WorkingAssembly where
  | ordinaryEnd (q : CutPhase) (terminal : List ℝ)
  | ordinary (q : CutPhase) (suffix : WorkingAssembly)
  | block (left : CutPhase) (inside : List ℝ) (connector : ℝ) (suffix : WorkingAssembly)
  | blockEnd (left : CutPhase) (inside : List ℝ) (connector : ℝ) (terminal : List ℝ)
  | noConnector (left : CutPhase) (inside terminal : List ℝ)

namespace WorkingAssembly

def word : WorkingAssembly → List ℝ
  | .ordinaryEnd q t => q.word++t
  | .ordinary q s => q.word++s.word
  | .block q I c s => q.word++((I++[c])++s.word)
  | .blockEnd q I c t => q.word++((I++[c])++t)
  | .noConnector q I t => q.word++(I++t)

def rate (A μ P : ℝ) : WorkingAssembly → ℝ
  | .ordinaryEnd q t => Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t)) *
      (ordinaryReferenceFactor A μ q.pivot P q.gap)^2
  | .ordinary q s => s.rate A μ P*(ordinaryReferenceFactor A μ q.pivot P q.gap)^2
  | .block _ I _ s => s.rate A μ P/(workingBlockFactor A μ I)^2
  | .blockEnd _ I _ t => workingTerminalRate A μ I t
  | .noConnector _ I t => workingNoConnectorRate A μ I t

def Valid (A μ T P : ℝ) : WorkingAssembly → Prop
  | .ordinaryEnd q t => OrdinaryPhaseParameters A μ q.pivot T P q.gap ∧ (∀ a ∈ t, 0 < a → a ≤ A)
  | .ordinary q s => OrdinaryPhaseParameters A μ q.pivot T P q.gap ∧ s.Valid A μ T P
  | .block q I c s => OrdinaryPhaseParameters A μ q.pivot T P q.gap ∧
      2 ≤ c ∧ c ≤ A^(2 : ℝ) ∧ 1/32 ≤ 1-μ*c ∧ (∀ a ∈ I, 1-μ*a ≠ 0) ∧ s.Valid A μ T P
  | .blockEnd q I c t => OrdinaryPhaseParameters A μ q.pivot T P q.gap ∧
      2 ≤ c ∧ 1/32 ≤ 1-μ*c ∧ (∀ a ∈ I, 1-μ*a ≠ 0) ∧ (∀ a ∈ t, 0 < a → a ≤ A)
  | .noConnector q I t => OrdinaryPhaseParameters A μ q.pivot T P q.gap ∧
      (∀ a ∈ I, 1-μ*a ≠ 0) ∧ (∀ a ∈ t, 0 < a → a ≤ A)

/-- Phases whose reference factors are retained in the assembled lower bound. -/
def tracked : WorkingAssembly → List CutPhase
  | .ordinaryEnd q _ => [q]
  | .ordinary q s => q :: s.tracked
  | .block _ _ _ s => s.tracked
  | .blockEnd _ _ _ _ => []
  | .noConnector _ _ _ => []

/-- Exceptional words are pairwise separate in this representation. -/
def blockWords : WorkingAssembly → List (List ℝ)
  | .ordinaryEnd _ _ => []
  | .ordinary _ s => s.blockWords
  | .block _ I _ s => I :: s.blockWords
  | .blockEnd _ I _ _ => [I]
  | .noConnector _ I _ => [I]

theorem eventually_realize : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ s : WorkingAssembly, s.Valid A μ T P →
      Nonempty (PositiveTrace μ s.word (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ)) (s.rate A μ P)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_ordinary_positive_trace,
    eventually_working_exceptional_trace,eventually_working_terminal_trace,eventually_working_no_connector_trace]
    with A hA hord hblock hterminal hno
  intro μ T P s
  induction s with
  | ordinaryEnd q t =>
    intro ⟨W,ht⟩
    obtain ⟨S⟩ := terminal_positive_trace W.mu_positive.le (W.mu_cap hA) t ht (workingGateFraction A)
    exact hord μ q.pivot T P q.gap W t _ _ _ S
  | ordinary q s ih =>
    intro ⟨W,hs⟩
    obtain ⟨S⟩ := ih hs
    exact hord μ q.pivot T P q.gap W s.word _ _ _ S
  | block q I c s ih =>
    intro ⟨W,hc,hcA,hqc,hcritical,hs⟩
    obtain ⟨S⟩ := ih hs
    exact hblock μ q.pivot T P c q.gap I W hc hcA hqc hcritical s.word _ S
  | blockEnd q I c t =>
    intro ⟨W,hc,hqc,hcritical,ht⟩
    exact hterminal μ q.pivot T P c q.gap I t W hc hqc hcritical ht
  | noConnector q I t =>
    intro ⟨W,hcritical,ht⟩
    exact hno μ q.pivot T P q.gap I t W hcritical ht

theorem eventually_distance_lower : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ s : WorkingAssembly, s.Valid A μ T P →
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → ENNReal.ofReal (s.rate A μ P) ≤ D κ s.word := by
  filter_upwards [eventually_realize] with A hrealize
  intro κ μ T P s hs hκ hμ hμ1
  obtain ⟨S⟩ := hrealize μ T P s hs
  exact S.distance_lower hκ hμ hμ1

theorem eventually_stable_rate : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ s : WorkingAssembly, s.Valid A μ T P →
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → D κ s.word ≤ 1 → s.rate A μ P ≤ 1 := by
  filter_upwards [eventually_realize] with A hrealize
  intro κ μ T P s hs hκ hμ hμ1 hD
  obtain ⟨S⟩ := hrealize μ T P s hs
  exact S.stable_ratio_le_one hκ hμ hμ1 hD

end WorkingAssembly
end
end StrongSilver
