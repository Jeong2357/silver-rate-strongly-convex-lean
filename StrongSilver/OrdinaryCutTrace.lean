-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScheduleCut
import StrongSilver.WorkingTraceOrdinary

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2200000

def ordinaryPhaseProduct (A μ P : ℝ) (qs : List CutPhase) : ℝ :=
  (qs.map fun q => ordinaryReferenceFactor A μ q.pivot P q.gap).prod

theorem ordinaryPhaseProduct_positive {A μ T P : ℝ} {qs : List CutPhase}
    (hA : 1 < A) (hgood : ∀ q ∈ qs, OrdinaryPhaseParameters A μ q.pivot T P q.gap) :
    0 < ordinaryPhaseProduct A μ P qs := by
  apply List.prod_pos
  intro z hz
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
  exact (hgood q hq).reference_factor_positive hA

/-- An arbitrary number of ordinary phases is realized with one uniform
large-cutoff threshold. The terminal gap is executed on an actual quadratic. -/
theorem eventually_ordinary_cut_trace : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ C : ScheduleCut,
      0 ≤ μ → μ*A ≤ 1/2 →
      (∀ q ∈ C.phases, OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      (∀ a ∈ C.terminal, 0 < a → a ≤ A) →
      ∃ M G : ℝ, Nonempty (PositiveTrace μ C.word (workingGateFraction A) M G
        (Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass C.terminal)) *
          (ordinaryPhaseProduct A μ P C.phases)^2)) := by
  filter_upwards [eventually_ordinary_positive_trace] with A hattach
  intro μ T P C hμ hcap hgood ht
  rcases C with ⟨qs,t⟩
  change ∀ q ∈ qs, OrdinaryPhaseParameters A μ q.pivot T P q.gap at hgood
  change ∀ a ∈ t, 0 < a → a ≤ A at ht
  induction qs with
  | nil =>
    refine ⟨maxPrefixProduct μ t,0,?_⟩
    simpa [ScheduleCut.word,ordinaryPhaseProduct] using
      terminal_positive_trace hμ hcap t ht (workingGateFraction A)
  | cons q qs ih =>
    have hq := hgood q (by simp)
    have hqs : ∀ z ∈ qs, OrdinaryPhaseParameters A μ z.pivot T P z.gap := by
      intro z hz
      exact hgood z (List.mem_cons_of_mem q hz)
    obtain ⟨M,G,⟨S⟩⟩ := ih hqs
    refine ⟨A^(10 : ℝ),A^(10 : ℝ),?_⟩
    have hh := hattach μ q.pivot T P q.gap hq _ M G _ S
    simpa [ScheduleCut.word,CutPhase.word,ordinaryPhaseProduct,List.append_assoc,
      mul_pow,mul_assoc,mul_comm,mul_left_comm] using hh

theorem eventually_ordinary_cut_distance_lower : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ C : ScheduleCut,
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → 0 ≤ μ → μ*A ≤ 1/2 →
      (∀ q ∈ C.phases, OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      (∀ a ∈ C.terminal, 0 < a → a ≤ A) →
      ENNReal.ofReal (Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass C.terminal)) *
        (ordinaryPhaseProduct A μ P C.phases)^2) ≤ D κ C.word := by
  filter_upwards [eventually_ordinary_cut_trace] with A htrace
  intro κ μ T P C hκ hμ hμ1 hμ0 hcap hgood ht
  obtain ⟨M,G,⟨S⟩⟩ := htrace μ T P C hμ0 hcap hgood ht
  exact S.distance_lower hκ hμ hμ1

theorem eventually_stable_ordinary_cut_product : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ C : ScheduleCut,
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → 0 ≤ μ → μ*A ≤ 1/2 →
      (∀ q ∈ C.phases, OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      (∀ a ∈ C.terminal, 0 < a → a ≤ A) → D κ C.word ≤ 1 →
      Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass C.terminal)) *
        (ordinaryPhaseProduct A μ P C.phases)^2 ≤ 1 := by
  filter_upwards [eventually_ordinary_cut_trace] with A htrace
  intro κ μ T P C hκ hμ hμ1 hμ0 hcap hgood ht hD
  obtain ⟨M,G,⟨S⟩⟩ := htrace μ T P C hμ0 hcap hgood ht
  exact S.stable_ratio_le_one hκ hμ hμ1 hD

end
end StrongSilver
