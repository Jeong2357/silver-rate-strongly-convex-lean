-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteCutAssembly
import StrongSilver.CutAssemblyRealization
import StrongSilver.WorkingOpenBlock

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

namespace CompleteCutAssembly

def word (t : List ℝ) (s : CompleteCutAssembly) : List ℝ := s.phases.flatMap CutPhase.word++t

def openTerminalRate (μ : ℝ) (I t : List ℝ) : ℝ :=
  Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))/
    ((4*(1200000 : ℝ)^2)*(Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I))^2)

def rate (A μ P : ℝ) (t : List ℝ) : CompleteCutAssembly → ℝ
  | .scalar I => Real.exp (-2*(inverseCharge μ (I.flatMap CutPhase.word)+2*μ*Scalar.SignedIntervals.positiveMass t))
  | .positive s => (s.erase t).rate A μ P
  | .leadingBlock I c s => (s.erase t).rate A μ P/(workingBlockFactor A μ (I.flatMap CutPhase.word++c.gap))^2
  | .leadingEnd I c => openTerminalRate μ (I.flatMap CutPhase.word++c.gap) t

theorem prefix_word (I : List CutPhase) (c : CutPhase) (s : CutAssembly) (t : List ℝ) :
    (.leadingBlock I c s : CompleteCutAssembly).word t =
      ((I.flatMap CutPhase.word++c.gap)++[c.pivot])++(s.phases.flatMap CutPhase.word++t) := by
  simp [word,phases,CutPhase.word,List.append_assoc]

theorem prefixEnd_word (I : List CutPhase) (c : CutPhase) (t : List ℝ) :
    (.leadingEnd I c : CompleteCutAssembly).word t = ((I.flatMap CutPhase.word++c.gap)++[c.pivot])++t := by
  simp [word,phases,CutPhase.word,List.append_assoc]

theorem eventually_distance_lower : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      ∀ s : CompleteCutAssembly, s.WellFormed good → ∀ t : List ℝ,
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ*A ≤ 1/2 →
      (∀ a ∈ t, 0 < a → a ≤ A) → (∀ a ∈ s.word t, 1-μ*a ≠ 0) →
      ENNReal.ofReal (s.rate A μ P t) ≤ D κ (s.word t) := by
  filter_upwards [CutAssembly.eventually_realize,eventually_ordinary_connector_bounds,
    eventually_working_open_block_distance_lower] with A hrealize hconn hopen
  intro κ μ T P good hW s hs t hκ hμ hμ1 hcap ht hcritical
  cases s with
  | scalar I =>
    exact open_scalar_distance_lower hκ hμ hμ1 hcap (I.flatMap CutPhase.word) t
      (fun a ha => hcritical a (List.mem_append_left _ ha)) ht
  | positive s =>
    obtain ⟨S⟩ := hrealize μ T P good hW s hs t ht hcritical
    exact S.distance_lower hκ hμ hμ1
  | leadingBlock I c s =>
    rw [prefix_word] at hcritical ⊢
    obtain ⟨hc,hcA,hqc⟩ := hconn μ c.pivot T P c.gap (hW c hs.1)
    have hcritSuffix : ∀ a ∈ s.phases.flatMap CutPhase.word++t, 1-μ*a ≠ 0 := by
      intro a ha
      exact hcritical a (List.mem_append_right _ ha)
    obtain ⟨S⟩ := hrealize μ T P good hW s hs.2 t ht hcritSuffix
    exact hopen κ μ c.pivot (I.flatMap CutPhase.word++c.gap) _ _ hκ hμ hμ1 hc hcA hqc
      (fun a ha => hcritical a (List.mem_append_left _ (List.mem_append_left _ ha))) S
  | leadingEnd I c =>
    rw [prefixEnd_word] at hcritical ⊢
    obtain ⟨hc,_,hqc⟩ := hconn μ c.pivot T P c.gap (hW c hs)
    exact open_terminal_distance_lower hκ hμ hμ1 hc hqc hcap (I.flatMap CutPhase.word++c.gap) t
      (fun a ha => hcritical a (List.mem_append_left _ (List.mem_append_left _ ha))) ht

end CompleteCutAssembly

def ordinaryPhaseGood (A μ T P : ℝ) (q : CutPhase) : Bool :=
  @decide (OrdinaryPhaseParameters A μ q.pivot T P q.gap) (Classical.propDecidable _)

/-- For every actual cut the reservation algorithm constructs an exact
last-iterate witness. The bound retains the explicit, unsummed block prices. -/
theorem eventually_every_cut_realizable : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ C : ScheduleCut,
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ*A ≤ 1/2 →
      (∀ a ∈ C.terminal, 0 < a → a ≤ A) → (∀ a ∈ C.word, 1-μ*a ≠ 0) →
      ∃ s : CompleteCutAssembly, s.phases = C.phases ∧
        s.WellFormed (ordinaryPhaseGood A μ T P) ∧
        s.reserved.length ≤ 4*badPhaseCount (ordinaryPhaseGood A μ T P) C.phases ∧
        ENNReal.ofReal (s.rate A μ P C.terminal) ≤ D κ C.word := by
  classical
  filter_upwards [CompleteCutAssembly.eventually_distance_lower] with A hlower
  intro κ μ T P C hκ hμ hμ1 hcap ht hcritical
  let good : CutPhase → Bool := ordinaryPhaseGood A μ T P
  obtain ⟨s,hph,hs,_,hcount⟩ := exists_complete_cutAssembly good C.phases
  refine ⟨s,hph,hs,hcount,?_⟩
  have hword : s.word C.terminal = C.word := by simp only [CompleteCutAssembly.word,hph,ScheduleCut.word]
  have hcrit' : ∀ a ∈ s.word C.terminal, 1-μ*a ≠ 0 := by simpa only [hword] using hcritical
  simpa only [hword] using hlower κ μ T P good (fun _ hq => of_decide_eq_true hq) s hs C.terminal
    hκ hμ hμ1 hcap ht hcrit'

end
end StrongSilver
