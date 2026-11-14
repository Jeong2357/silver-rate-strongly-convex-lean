-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteCutLog
import StrongSilver.WorkingReplacementLog

namespace StrongSilver.CompleteCutAssembly
open Real Filter
noncomputable section
set_option maxHeartbeats 4000000

/-- The replacement is an actual trace on the original nonreserved
suffix. The leading reservation is handled by the existing open-block
construction; cases with no tracked phases permit only nonpositive gain. -/
def ReplacementWitness (A μ P : ℝ) (t : List ℝ) (gain : ℝ) : CompleteCutAssembly → Prop
  | .scalar _ => gain ≤ 0
  | .positive s => Nonempty (PositiveTrace μ (s.phases.flatMap CutPhase.word++t) (workingGateFraction A)
      (A^(10:ℝ)) (A^(10:ℝ)) ((s.erase t).rate A μ P*Real.exp gain))
  | .leadingBlock _ _ s => Nonempty (PositiveTrace μ (s.phases.flatMap CutPhase.word++t) (workingGateFraction A)
      (A^(10:ℝ)) (A^(10:ℝ)) ((s.erase t).rate A μ P*Real.exp gain))
  | .leadingEnd _ _ => gain ≤ 0

/-- A local improvement of the actual positive suffix is inserted into
the complete original schedule, including all leading exceptional steps. -/
theorem eventually_replacement_distance_lower : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ good : CutPhase → Bool,
    (∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
    ∀ s : CompleteCutAssembly, s.WellFormed good → ∀ t : List ℝ, ∀ gain : ℝ,
    1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ*A ≤ 1/2 →
    (∀ a ∈ t, 0 < a → a ≤ A) → (∀ a ∈ s.word t, 1-μ*a ≠ 0) →
    s.ReplacementWitness A μ P t gain →
    ENNReal.ofReal (s.rate A μ P t*Real.exp gain) ≤ D κ (s.word t) := by
  filter_upwards [eventually_distance_lower,eventually_ordinary_connector_bounds,
    eventually_working_open_block_distance_lower] with A hbaseline hconn hopen
  intro κ μ T P good hW s hs t gain hκ hμ hμ1 hcap ht hcritical hwitness
  have hbase := hbaseline κ μ T P good hW s hs t hκ hμ hμ1 hcap ht hcritical
  cases s with
  | scalar I =>
    have hgain : Real.exp gain ≤ 1 := Real.exp_le_one_iff.mpr hwitness
    have hr : 0 ≤ (.scalar I : CompleteCutAssembly).rate A μ P t := (Real.exp_pos _).le
    exact (ENNReal.ofReal_le_ofReal (by nlinarith only [mul_le_mul_of_nonneg_left hgain hr])).trans hbase
  | positive s =>
    obtain ⟨W⟩ := hwitness
    exact W.distance_lower hκ hμ hμ1
  | leadingBlock I c s =>
    obtain ⟨W⟩ := hwitness
    rw [prefix_word] at hcritical ⊢
    obtain ⟨hc,hcA,hqc⟩ := hconn μ c.pivot T P c.gap (hW c hs.1)
    have hh := hopen κ μ c.pivot (I.flatMap CutPhase.word++c.gap) _ _ hκ hμ hμ1 hc hcA hqc
      (fun a ha => hcritical a (List.mem_append_left _ (List.mem_append_left _ ha))) W
    have he : (.leadingBlock I c s : CompleteCutAssembly).rate A μ P t*Real.exp gain =
        ((s.erase t).rate A μ P*Real.exp gain)/(workingBlockFactor A μ (I.flatMap CutPhase.word++c.gap))^2 := by
      unfold rate
      ring
    rw [he]
    exact hh
  | leadingEnd I c =>
    have hgain : Real.exp gain ≤ 1 := Real.exp_le_one_iff.mpr hwitness
    have hr : 0 ≤ (.leadingEnd I c : CompleteCutAssembly).rate A μ P t := (openTerminalRate_positive _ _ _).le
    exact (ENNReal.ofReal_le_ofReal (by nlinarith only [mul_le_mul_of_nonneg_left hgain hr])).trans hbase

/-- Full-cut local-replacement test (the construction component of
(4.6)). Its premise is an actual finite trajectory witness, and its
right-hand side is the original reservation price. -/
theorem eventually_stable_replacement_test : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ good : CutPhase → Bool,
    (∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
    ∀ s : CompleteCutAssembly, s.WellFormed good → ∀ t : List ℝ, ∀ gain : ℝ,
    1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ*A ≤ 1/2 →
    (∀ a ∈ t, 0 < a → a ≤ A) → (∀ a ∈ s.word t, 1-μ*a ≠ 0) →
    s.ReplacementWitness A μ P t gain → D κ (s.word t) ≤ 1 →
    gain ≤ s.logCost A μ P t-2*s.referenceLog μ P t := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_replacement_distance_lower,eventually_phaseValid]
    with A hA hbound hvalid
  intro κ μ T P good hW s hs t gain hκ hμ hμ1 hcap ht hcritical hwitness hD
  have hlow := (hbound κ μ T P good hW s hs t gain hκ hμ hμ1 hcap ht hcritical hwitness).trans hD
  have hv := hvalid μ T P good hW s hs t ht hcritical
  have hr := rate_positive hA hv
  have hreal : s.rate A μ P t*Real.exp gain ≤ 1 := by
    have hh := ENNReal.toReal_mono ENNReal.one_ne_top hlow
    simpa only [ENNReal.toReal_ofReal (mul_pos hr (Real.exp_pos _)).le,ENNReal.toReal_one] using hh
  have hlog := Real.log_le_log (mul_pos hr (Real.exp_pos _)) hreal
  rw [Real.log_mul hr.ne' (Real.exp_ne_zero _),Real.log_exp,Real.log_one,log_rate hA hv] at hlog
  linarith only [hlog]

end
end StrongSilver.CompleteCutAssembly
