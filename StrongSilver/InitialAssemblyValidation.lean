-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialAssemblyTrace

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

theorem InitialPhaseBudget.connector_bounds {B μ b T κ : ℝ} {h : List ℝ}
    (W : InitialPhaseBudget B μ b T κ B h) (hB : 2 ≤ B) :
    2 ≤ b ∧ B ≤ b ∧ b ≤ κ ∧ 1/32 ≤ 1-μ*b := by
  have hh := mul_le_mul_of_nonneg_left W.pivot_lt_time.le W.mu_positive.le
  exact ⟨hB.trans W.pivot_lower,W.pivot_lower,by linarith only [W.pivot_upper,W.kappa_positive],
    by linarith only [hh,W.curvature]⟩

namespace InitialCutAssembly

theorem valid_of_wellFormed {A κ B μ T P : ℝ} {good : CutPhase → Bool}
    (hB : 2 ≤ B) (hW : ∀ q, good q = true → InitialPhaseBudget B μ q.pivot T κ B q.gap)
    (s : InitialCutAssembly) (hs : s.WellFormed good) (refine : CutPhase → List CutPhase)
    (hr : ∀ q ∈ s.trackedPhases, ∀ z ∈ refine q, OrdinaryPhaseParameters A μ z.pivot T P z.gap)
    (t : List ℝ) (hcritical : ∀ a ∈ s.phases.flatMap CutPhase.word++t, 1-μ*a ≠ 0) :
    s.Valid A κ B μ T P refine := by
  induction s with
  | terminal => trivial
  | tracked q s ih =>
    refine ⟨hr q (by simp [trackedPhases]),ih hs.2 (fun z hz => hr z (List.mem_cons_of_mem q hz)) ?_⟩
    intro a ha
    apply hcritical a
    simp only [phases,List.flatMap_cons,List.mem_append] at ⊢
    rcases List.mem_append.mp ha with ha | ha
    · exact Or.inl (Or.inr ha)
    · exact Or.inr ha
  | block q I c d s ih =>
    have Wc := hW c hs.2.1
    obtain ⟨hc,hcB,hcκ,hqc⟩ := Wc.connector_bounds hB
    refine ⟨hW q hs.1,hW d hs.2.2.1,hc,hcB,hcκ,hqc,?_,ih hs.2.2.2 hr ?_⟩
    · intro a ha
      apply hcritical a
      simp only [phases,List.flatMap_cons,List.flatMap_append,CutPhase.word,List.mem_append,List.mem_singleton] at ha ⊢
      aesop
    · intro a ha
      apply hcritical a
      simp only [phases,List.flatMap_cons,List.flatMap_append,List.mem_append] at ha ⊢
      aesop
  | terminalBlock q I c =>
    obtain ⟨hc,hcB,_,hqc⟩ := (hW c hs.2).connector_bounds hB
    refine ⟨hW q hs.1,hc,hcB,hqc,?_⟩
    intro a ha
    apply hcritical a
    simp only [phases,List.flatMap_cons,List.flatMap_append,List.flatMap_nil,CutPhase.word,List.mem_append,List.mem_singleton,List.not_mem_nil] at ha ⊢
    aesop
  | noConnector q I =>
    refine ⟨hW q hs,?_⟩
    intro a ha
    apply hcritical a
    simp only [phases,List.flatMap_cons,List.mem_append]
    exact Or.inl (Or.inr ha)

theorem eventually_original_word_distance_lower : ∀ᶠ A : ℝ in Filter.atTop,
    ∀ κ B μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → InitialPhaseBudget B μ q.pivot T κ B q.gap) →
      ∀ s : InitialCutAssembly, s.WellFormed good → ∀ refine : CutPhase → List CutPhase,
      (∀ q ∈ s.trackedPhases, (refine q).flatMap CutPhase.word = q.word) →
      (∀ q ∈ s.trackedPhases, ∀ z ∈ refine q, OrdinaryPhaseParameters A μ z.pivot T P z.gap) →
      ∀ t : List ℝ, A ≤ B → 2 ≤ B → κ ≤ A^((1003 : ℝ)/1000) →
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ*B ≤ 1/2 →
      (∀ a ∈ t, 0 < a → a ≤ B) → (∀ a ∈ s.phases.flatMap CutPhase.word++t, 1-μ*a ≠ 0) →
      ENNReal.ofReal (s.rate A κ B μ P refine t) ≤ D κ (s.phases.flatMap CutPhase.word++t) := by
  filter_upwards [eventually_realize] with A hrealize
  intro κ B μ T P good hW s hs refine hr hparams t hAB hB hκA hκ hμ hμ1 hcap ht hcritical
  have hμ0 : 0 ≤ μ := (one_div_pos.mpr (zero_lt_one.trans_le hκ)).le.trans hμ
  obtain ⟨M,G,⟨S⟩⟩ := hrealize κ B μ T P refine s t hAB hκA hμ0 hcap ht
    (s.valid_of_wellFormed hB hW hs refine hparams t hcritical)
  have hh := S.distance_lower hκ hμ hμ1
  simpa only [word,s.expanded_word refine hr] using hh

end InitialCutAssembly
end
end StrongSilver
