-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TraceLogPrices

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3600000

/-- A concrete local operation is required to extend every actual
retained positive suffix, with the original word and renewed working
bounds. Its factor is independent of that retained suffix. -/
def PhaseTraceExtension (A μ : ℝ) (q : CutPhase) (factor : ℝ) : Prop :=
  ∀ h : List ℝ, ∀ M G r : ℝ, 0 ≤ r → PositiveTrace μ h (workingGateFraction A) M G r →
    Nonempty (PositiveTrace μ (q.word++h) (workingGateFraction A) (A^(10:ℝ)) (A^(10:ℝ)) (r*factor))

namespace WorkingAssembly

def replacementRate (A μ P : ℝ) (f : CutPhase → ℝ) : WorkingAssembly → ℝ
  | .ordinaryEnd q t => Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))*f q
  | .ordinary q s => s.replacementRate A μ P f*f q
  | .block _ I _ s => s.replacementRate A μ P f/(workingBlockFactor A μ I)^2
  | .blockEnd _ I _ t => workingTerminalRate A μ I t
  | .noConnector _ I t => workingNoConnectorRate A μ I t

theorem tracked_parameters {A μ T P : ℝ} {s : WorkingAssembly} (hs : s.Valid A μ T P) :
    ∀ q ∈ s.tracked, OrdinaryPhaseParameters A μ q.pivot T P q.gap := by
  induction s with
  | ordinaryEnd q t =>
    intro p hp
    simp only [tracked,List.mem_singleton] at hp
    subst p
    exact hs.1
  | ordinary q s ih =>
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst p; exact hs.1
    · exact ih hs.2 p hp
  | block q I c s ih => exact ih hs.2.2.2.2.2
  | blockEnd q I c t => simp [tracked]
  | noConnector q I t => simp [tracked]

theorem replacementRate_positive {A μ T P : ℝ} {s : WorkingAssembly} (hA : 0 < A)
    (hs : s.Valid A μ T P) {f : CutPhase → ℝ} (hf : ∀ q ∈ s.tracked, 0 < f q) :
    0 < s.replacementRate A μ P f := by
  induction s with
  | ordinaryEnd q t => exact mul_pos (Real.exp_pos _) (hf q (by simp [tracked]))
  | ordinary q s ih =>
    exact mul_pos (ih hs.2 (fun q hq => hf q (List.mem_cons_of_mem _ hq))) (hf q (by simp [tracked]))
  | block q I c s ih => exact div_pos (ih hs.2.2.2.2.2 hf) (sq_pos_of_pos (workingBlockFactor_positive hA _ _))
  | blockEnd q I c t => exact workingTerminalRate_positive hA _ _ _
  | noConnector q I t => exact workingNoConnectorRate_positive hA _ _ _

/-- Local replacements change only the ordinary factors. The exceptional
blocks and their original reservation/critical-step conditions are
realized with exactly the same explicit costs. -/
theorem eventually_realize_replacements : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ s : WorkingAssembly, s.Valid A μ T P →
    ∀ f : CutPhase → ℝ, (∀ q ∈ s.tracked, 0 < f q) →
    (∀ q ∈ s.tracked, PhaseTraceExtension A μ q (f q)) →
    Nonempty (PositiveTrace μ s.word (workingGateFraction A) (A^(10:ℝ)) (A^(10:ℝ))
      (s.replacementRate A μ P f)) := by
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_working_exceptional_trace,
    eventually_working_terminal_trace,eventually_working_no_connector_trace]
    with A hA hblock hterminal hno
  intro μ T P s
  induction s with
  | ordinaryEnd q t =>
    intro ⟨W,ht⟩ f hf hext
    obtain ⟨S⟩ := terminal_positive_trace W.mu_positive.le (W.mu_cap hA) t ht (workingGateFraction A)
    exact hext q (by simp [tracked]) t _ _ _ (Real.exp_pos _).le S
  | ordinary q s ih =>
    intro ⟨W,hs⟩ f hf hext
    have hft : ∀ q ∈ s.tracked, 0 < f q := fun q hq => hf q (List.mem_cons_of_mem _ hq)
    have het : ∀ q ∈ s.tracked, PhaseTraceExtension A μ q (f q) := fun q hq => hext q (List.mem_cons_of_mem _ hq)
    obtain ⟨S⟩ := ih hs f hft het
    exact hext q (by simp [tracked]) s.word _ _ _ (replacementRate_positive hA hs hft).le S
  | block q I c s ih =>
    intro ⟨W,hc,hcA,hqc,hcritical,hs⟩ f hf hext
    obtain ⟨S⟩ := ih hs f hf hext
    exact hblock μ q.pivot T P c q.gap I W hc hcA hqc hcritical s.word _ S
  | blockEnd q I c t =>
    intro ⟨W,hc,hqc,hcritical,ht⟩ f hf hext
    exact hterminal μ q.pivot T P c q.gap I t W hc hqc hcritical ht
  | noConnector q I t =>
    intro ⟨W,hcritical,ht⟩ f hf hext
    exact hno μ q.pivot T P q.gap I t W hcritical ht

end WorkingAssembly
end
end StrongSilver
