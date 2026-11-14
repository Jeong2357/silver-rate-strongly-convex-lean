-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialCutAssembly
import StrongSilver.InitialReservedTrace
import StrongSilver.OrdinaryTraceChain

namespace StrongSilver.InitialCutAssembly
open Real Filter
noncomputable section
set_option maxHeartbeats 2600000

/-- Refinement is applied only to tracked original phases. -/
def expandedPhases (refine : CutPhase → List CutPhase) : InitialCutAssembly → List CutPhase
  | .terminal => []
  | .tracked q s => refine q++s.expandedPhases refine
  | .block q I c d s => q::(I++(c::d::s.expandedPhases refine))
  | .terminalBlock q I c => q::(I++[c])
  | .noConnector q I => q::I

def word (refine : CutPhase → List CutPhase) (t : List ℝ) (s : InitialCutAssembly) : List ℝ :=
  (s.expandedPhases refine).flatMap CutPhase.word++t

def rate (A κ B μ P : ℝ) (refine : CutPhase → List CutPhase) (t : List ℝ) : InitialCutAssembly → ℝ
  | .terminal => Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))
  | .tracked q s => s.rate A κ B μ P refine t*(ordinaryPhaseProduct A μ P (refine q))^2
  | .block _ I c _ s => initialReservedRate κ B μ (I.flatMap CutPhase.word++c.gap) (s.rate A κ B μ P refine t)
  | .terminalBlock _ I c => initialTerminalRate κ B μ (I.flatMap CutPhase.word++c.gap) t
  | .noConnector _ I => initialNoConnectorRate κ B μ (I.flatMap CutPhase.word) t

def Valid (A κ B μ T P : ℝ) (refine : CutPhase → List CutPhase) : InitialCutAssembly → Prop
  | .terminal => True
  | .tracked q s => (∀ z ∈ refine q, OrdinaryPhaseParameters A μ z.pivot T P z.gap) ∧ s.Valid A κ B μ T P refine
  | .block q I c d s => InitialPhaseBudget B μ q.pivot T κ B q.gap ∧ InitialPhaseBudget B μ d.pivot T κ B d.gap ∧
      2 ≤ c.pivot ∧ B ≤ c.pivot ∧ c.pivot ≤ κ ∧ 1/32 ≤ 1-μ*c.pivot ∧
      (∀ a ∈ I.flatMap CutPhase.word++c.gap, 1-μ*a ≠ 0) ∧ s.Valid A κ B μ T P refine
  | .terminalBlock q I c => InitialPhaseBudget B μ q.pivot T κ B q.gap ∧
      2 ≤ c.pivot ∧ B ≤ c.pivot ∧ 1/32 ≤ 1-μ*c.pivot ∧ (∀ a ∈ I.flatMap CutPhase.word++c.gap, 1-μ*a ≠ 0)
  | .noConnector q I => InitialPhaseBudget B μ q.pivot T κ B q.gap ∧ (∀ a ∈ I.flatMap CutPhase.word, 1-μ*a ≠ 0)

theorem expanded_word (s : InitialCutAssembly) (refine : CutPhase → List CutPhase)
    (hr : ∀ q ∈ s.trackedPhases, (refine q).flatMap CutPhase.word = q.word) :
    (s.expandedPhases refine).flatMap CutPhase.word = s.phases.flatMap CutPhase.word := by
  induction s with
  | terminal => rfl
  | tracked q s ih =>
    have hq := hr q (by simp [trackedPhases])
    have hs := ih (fun z hz => hr z (List.mem_cons_of_mem q hz))
    simp only [expandedPhases,phases,List.flatMap_append,List.flatMap_cons,hq,hs]
  | block q I c d s ih =>
    have hs := ih hr
    simp only [expandedPhases,phases,List.flatMap_cons,List.flatMap_append,hs]
  | terminalBlock q I c => rfl
  | noConnector q I => rfl

/-- Every finite assembly uses the original B-scale for reserved roles
and the refined A-scale for tracked descendants, on one actual path. -/
theorem eventually_realize : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ T P : ℝ, ∀ refine : CutPhase → List CutPhase, ∀ s : InitialCutAssembly, ∀ t : List ℝ,
      A ≤ B → κ ≤ A^((1003 : ℝ)/1000) → 0 ≤ μ → μ*B ≤ 1/2 →
      (∀ a ∈ t, 0 < a → a ≤ B) → s.Valid A κ B μ T P refine →
      ∃ M G : ℝ, Nonempty (PositiveTrace μ (s.word refine t) (workingGateFraction A) M G (s.rate A κ B μ P refine t)) := by
  filter_upwards [eventually_ordinary_prepend_chain,eventually_initial_reserved_trace,
    eventually_initial_terminal_working_trace,eventually_initial_no_connector_working_trace]
    with A hord hblock hterminal hno
  intro κ B μ T P refine s t hAB hκA hμ hcap ht
  induction s with
  | terminal =>
    intro _
    exact ⟨maxPrefixProduct μ t,0,terminal_positive_trace hμ hcap t ht (workingGateFraction A)⟩
  | tracked q s ih =>
    intro ⟨hq,hs⟩
    obtain ⟨M,G,⟨S⟩⟩ := ih hs
    obtain ⟨M',G',htrace⟩ := hord μ T P (refine q) hq _ M G _ S
    exact ⟨M',G',by simpa [word,expandedPhases,rate,List.append_assoc] using htrace⟩
  | block q I c d s ih =>
    intro ⟨W,Wd,hc,hcB,hcκ,hqc,hcritical,hs⟩
    obtain ⟨M,G,⟨S⟩⟩ := ih hs
    have hh := hblock κ B μ q.pivot T c.pivot d.pivot T q.gap (I.flatMap CutPhase.word++c.gap) d.gap
      hAB hκA W Wd hc hcB hcκ hqc hcritical _ M G _ S
    refine ⟨A^(10 : ℝ),A^(10 : ℝ),?_⟩
    simpa [word,expandedPhases,rate,CutPhase.word,List.append_assoc] using hh
  | terminalBlock q I c =>
    intro ⟨W,hc,hcB,hqc,hcritical⟩
    have hh := hterminal κ B μ q.pivot T c.pivot q.gap (I.flatMap CutPhase.word++c.gap) t
      hAB hκA W hc hcB hqc hcap hcritical ht
    refine ⟨A^(10 : ℝ),A^(10 : ℝ),?_⟩
    simpa [word,expandedPhases,rate,CutPhase.word,List.append_assoc] using hh
  | noConnector q I =>
    intro ⟨W,hcritical⟩
    have hh := hno κ B μ q.pivot T q.gap (I.flatMap CutPhase.word) t hAB hκA W hcap hcritical ht
    refine ⟨A^(10 : ℝ),A^(10 : ℝ),?_⟩
    simpa [word,expandedPhases,rate,CutPhase.word,List.append_assoc] using hh

end
end StrongSilver.InitialCutAssembly
