-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteInitialCutAssembly
import StrongSilver.InitialOpenTerminal
import StrongSilver.InitialRefinedCutTrace
import StrongSilver.WorkingOpenBlock

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2600000

namespace CompleteInitialCutAssembly

def word (t : List ℝ) (s : CompleteInitialCutAssembly) : List ℝ := s.phases.flatMap CutPhase.word++t

def rate (A κ B μ P : ℝ) (choose : ℕ → ℝ → Bool) (t : List ℝ) : CompleteInitialCutAssembly → ℝ
  | .scalar I => Real.exp (-2*(inverseCharge μ (I.flatMap CutPhase.word)+2*μ*Scalar.SignedIntervals.positiveMass t))
  | .positive s => s.rate A κ B μ P (refinePhase choose) t
  | .leadingBlock I c _ s => initialReservedRate κ B μ (I.flatMap CutPhase.word++c.gap) (s.rate A κ B μ P (refinePhase choose) t)
  | .leadingEnd I c => initialOpenTerminalRate κ B μ (I.flatMap CutPhase.word++c.gap) t

theorem leading_word (I : List CutPhase) (c d : CutPhase) (s : InitialCutAssembly) (t : List ℝ) :
    (.leadingBlock I c d s : CompleteInitialCutAssembly).word t =
      ((I.flatMap CutPhase.word++c.gap)++[c.pivot])++(d.word++(s.phases.flatMap CutPhase.word++t)) := by
  simp [word,phases,CutPhase.word,List.append_assoc]

theorem leadingEnd_word (I : List CutPhase) (c : CutPhase) (t : List ℝ) :
    (.leadingEnd I c : CompleteInitialCutAssembly).word t = ((I.flatMap CutPhase.word++c.gap)++[c.pivot])++t := by
  simp [word,phases,CutPhase.word,List.append_assoc]

theorem eventually_distance_lower : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → InitialPhaseBudget B μ q.pivot T κ B q.gap) →
      ∀ s : CompleteInitialCutAssembly, s.WellFormed good → ∀ choose : ℕ → ℝ → Bool, ∀ t : List ℝ,
      A ≤ B → 2 ≤ B → κ ≤ A^((1003 : ℝ)/1000) →
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ*B ≤ 1/2 →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ i b, choose i b = true → A ≤ b) → (∀ i b, choose i b = false → 0 < b → b ≤ A) →
      (∀ a ∈ t, 0 < a → a ≤ B) → (∀ a ∈ s.word t, 1-μ*a ≠ 0) →
      ENNReal.ofReal (s.rate A κ B μ P choose t) ≤ D κ (s.word t) := by
  filter_upwards [InitialCutAssembly.eventually_realize,eventually_initial_refined_parameters,
    eventually_initial_open_reserved_lower] with A hrealize hparams hopen
  intro κ B μ T P good hW s hs choose t hAB hB hκA hκ hμ hμ1 hcap hPL hPU hselected hunselected ht hcritical
  have hμ0 : 0 ≤ μ := (one_div_pos.mpr (zero_lt_one.trans_le hκ)).le.trans hμ
  have buildPositive (S : InitialCutAssembly) (hS : S.WellFormed good)
      (hcrit : ∀ a ∈ S.phases.flatMap CutPhase.word++t, 1-μ*a ≠ 0) :
      ∃ M G : ℝ, Nonempty (PositiveTrace μ (S.phases.flatMap CutPhase.word++t) (workingGateFraction A) M G
        (S.rate A κ B μ P (refinePhase choose) t)) := by
    have ho : ∀ z ∈ S.trackedPhases, ∀ w ∈ refinePhase choose z, OrdinaryPhaseParameters A μ w.pivot T P w.gap := by
      intro z hz
      exact hparams κ B μ T P z choose hAB hκA hPL hPU (hW z (S.tracked_good hS z hz)) hselected hunselected
    obtain ⟨M,G,htrace⟩ := hrealize κ B μ T P (refinePhase choose) S t hAB hκA hμ0 hcap ht
      (S.valid_of_wellFormed hB hW hS (refinePhase choose) ho t hcrit)
    refine ⟨M,G,?_⟩
    simpa only [InitialCutAssembly.word,S.expanded_word (refinePhase choose) (fun q _ => refinePhase_word choose q)] using htrace
  cases s with
  | scalar I =>
    exact open_scalar_distance_lower hκ hμ hμ1 hcap (I.flatMap CutPhase.word) t
      (fun a ha => hcritical a (List.mem_append_left _ ha)) ht
  | positive S =>
    obtain ⟨M,G,⟨Q⟩⟩ := buildPositive S hs hcritical
    exact Q.distance_lower hκ hμ hμ1
  | leadingBlock I c d S =>
    rw [leading_word] at hcritical ⊢
    obtain ⟨hc,hcB,hcκ,hqc⟩ := (hW c hs.1).connector_bounds hB
    have hcritSuffix : ∀ a ∈ S.phases.flatMap CutPhase.word++t, 1-μ*a ≠ 0 := by
      intro a ha
      exact hcritical a (List.mem_append_right _ (List.mem_append_right _ ha))
    obtain ⟨M,G,⟨Q⟩⟩ := buildPositive S hs.2.2 hcritSuffix
    exact hopen κ B μ c.pivot d.pivot T (I.flatMap CutPhase.word++c.gap) d.gap hAB hκA (hW d hs.2.1)
      hμ hμ1 hc hcB hcκ hqc (fun a ha => hcritical a (List.mem_append_left _ (List.mem_append_left _ ha))) _ M G _ Q
  | leadingEnd I c =>
    rw [leadingEnd_word] at hcritical ⊢
    have Wc := hW c hs
    obtain ⟨hc,hcB,_,hqc⟩ := Wc.connector_bounds hB
    exact initial_open_terminal_distance_lower hκ Wc.B_positive Wc.B_le_kappa hμ hμ1 hc hcB hqc hcap
      (I.flatMap CutPhase.word++c.gap) t (fun a ha => hcritical a (List.mem_append_left _ (List.mem_append_left _ ha))) ht

end CompleteInitialCutAssembly

/-- Every original initial cut admits an actual tracked-only refined
trajectory, including a marked first phase and both terminal cases. -/
theorem eventually_every_initial_cut_realizable : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ T P : ℝ, ∀ C : ScheduleCut, ∀ choose : ℕ → ℝ → Bool,
      A ≤ B → 2 ≤ B → κ ≤ A^((1003 : ℝ)/1000) →
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ*B ≤ 1/2 →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ i b, choose i b = true → A ≤ b) → (∀ i b, choose i b = false → 0 < b → b ≤ A) →
      (∀ a ∈ C.terminal, 0 < a → a ≤ B) → (∀ a ∈ C.word, 1-μ*a ≠ 0) →
      ∃ s : CompleteInitialCutAssembly, s.phases = C.phases ∧ s.WellFormed (initialPhaseGood κ B μ T) ∧
        s.Counted (initialPhaseGood κ B μ T) ∧
        s.reserved.length ≤ 7*badPhaseCount (initialPhaseGood κ B μ T) C.phases ∧
        ENNReal.ofReal (s.rate A κ B μ P choose C.terminal) ≤ D κ C.word := by
  classical
  filter_upwards [CompleteInitialCutAssembly.eventually_distance_lower] with A hlower
  intro κ B μ T P C choose hAB hB hκA hκ hμ hμ1 hcap hPL hPU hselected hunselected ht hcritical
  let good := initialPhaseGood κ B μ T
  have hW : ∀ q, good q = true → InitialPhaseBudget B μ q.pivot T κ B q.gap := fun _ hq => of_decide_eq_true hq
  obtain ⟨s,hph,hs,hc,hcount⟩ := exists_complete_initial_cutAssembly good C.phases
  have hword : s.word C.terminal = C.word := by simp only [CompleteInitialCutAssembly.word,hph,ScheduleCut.word]
  refine ⟨s,hph,hs,hc,hcount,?_⟩
  have hcrit' : ∀ a ∈ s.word C.terminal, 1-μ*a ≠ 0 := by simpa only [hword] using hcritical
  simpa only [hword] using hlower κ B μ T P good hW s hs choose C.terminal hAB hB hκA hκ hμ hμ1 hcap
    hPL hPU hselected hunselected ht hcrit'

end
end StrongSilver
