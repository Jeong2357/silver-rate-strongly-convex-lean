-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.MaskedLinkedFrontier
import StrongSilver.FiniteBooleanIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5400000

def linkedFrontierTests (φ : ℝ → ℝ) (P : ℝ) (start : ℕ) (κ : ℝ) (t : ScheduleTree) : List (ℝ → Bool) :=
  (labels (t.indexedTree start κ)).map fun q => fun y => decide (P+Real.exp y < φ q.pivot)

theorem linkedFrontierTests_measurable (φ : ℝ → ℝ) (P : ℝ) (start : ℕ) (κ : ℝ) (t : ScheduleTree) :
    ∀ test ∈ linkedFrontierTests φ P start κ t, MeasurableSet {y | test y = true} := by
  intro test ht
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp ht
  simp only [decide_eq_true_eq]
  exact (isOpen_lt (continuous_const.add Real.continuous_exp) continuous_const).measurableSet

theorem linkedFrontierTests_eval (φ : ℝ → ℝ) (P : ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) (y : ℝ) :
    maskedLinkedFrontier start κ parent following t ((linkedFrontierTests φ P start κ t).map fun test => test y) =
      linkedFrontier φ (P+Real.exp y) start κ parent following t := by
  simp only [linkedFrontierTests,List.map_map,Function.comp_def]
  exact maskedLinkedFrontier_actual φ (P+Real.exp y) start κ parent following t

/-- An arbitrary real observable of the whole finite linked frontier
is measurable when each fixed frontier has a measurable score. This
includes adjacent-pair counts and finite gain sums. -/
theorem linkedFrontier_general_measurable (F : List LinkedGap → ℝ → ℝ) (hF : ∀ qs, Measurable (F qs))
    (φ : ℝ → ℝ) (P : ℝ) (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree) :
    Measurable (fun y => F (linkedFrontier φ (P+Real.exp y) start κ parent following t) y) := by
  let tests := linkedFrontierTests φ P start κ t
  let FF := fun bs : List Bool => F (maskedLinkedFrontier start κ parent following t bs)
  have hRes := measurable_finite_boolean_evaluation tests (linkedFrontierTests_measurable φ P start κ t)
    FF (fun bs => hF _)
  have he : (fun y => F (linkedFrontier φ (P+Real.exp y) start κ parent following t) y) =
      fun y => FF (tests.map fun test => test y) y := by
    funext y
    dsimp only [FF,tests]
    rw [linkedFrontierTests_eval]
  rw [he]
  exact hRes

/-- Interval integrability also passes through the finite frontier
selection. No measurability assumption on gap or reservation metadata
is introduced. -/
theorem linkedFrontier_general_integrable (F : List LinkedGap → ℝ → ℝ) (hF : ∀ qs, Measurable (F qs))
    (φ : ℝ → ℝ) (P : ℝ) (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree)
    (a b : ℝ) (hFi : ∀ qs, IntervalIntegrable (F qs) volume a b) :
    IntervalIntegrable (fun y => F (linkedFrontier φ (P+Real.exp y) start κ parent following t) y) volume a b := by
  let tests := linkedFrontierTests φ P start κ t
  let FF := fun bs : List Bool => F (maskedLinkedFrontier start κ parent following t bs)
  have hRes := intervalIntegrable_finite_boolean_evaluation tests (linkedFrontierTests_measurable φ P start κ t)
    FF (fun bs => hF _) a b (fun bs => hFi _)
  have he : (fun y => F (linkedFrontier φ (P+Real.exp y) start κ parent following t) y) =
      fun y => FF (tests.map fun test => test y) y := by
    funext y
    dsimp only [FF,tests]
    rw [linkedFrontierTests_eval]
  rw [he]
  exact hRes

end
end StrongSilver
