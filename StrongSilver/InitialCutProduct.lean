-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialNumericalCutBound

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2200000

def initialCutProductConstant : ℝ := 4864+7*(initialLogPriceConstant+6)

theorem initialCutProductConstant_bounds : 0 < initialCutProductConstant ∧ 4800 ≤ initialCutProductConstant ∧
    6 ≤ initialCutProductConstant ∧ 7*(initialLogPriceConstant+6)+64 ≤ initialCutProductConstant := by
  have hh := initialLogPriceConstant_positive
  unfold initialCutProductConstant
  constructor
  · linarith only [hh]
  constructor
  · linarith only [hh]
  constructor <;> linarith only [hh]

/-- The initial-cut product bound (3.30), with a fixed absolute constant
and the original cutoff logarithm. Every omitted phase is still executed
inside its reserved block. -/
theorem eventually_initial_cut_product_bound : ∀ᶠ A : ℝ in atTop,
    ∀ κ B P : ℝ, ∀ C : ScheduleCut, ∀ choose : ℕ → ℝ → Bool,
      A ≤ B → 2 ≤ B → B ≤ κ/4 → κ ≤ A^((1003 : ℝ)/1000) → 1 ≤ κ →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ q ∈ C.phases, B ≤ q.pivot) → (∀ b ∈ C.unselected, 0 < b → b ≤ B) →
      (∀ i b, choose i b = true → A ≤ b) → (∀ i b, choose i b = false → 0 < b → b ≤ A) →
      ∃ μ : ℝ, ∃ s : CompleteInitialCutAssembly,
        1/κ ≤ μ ∧ μ ≤ 9/(8*κ) ∧ (∀ b ∈ C.word, 1-μ*b ≠ 0) ∧ s.phases = C.phases ∧
        s.reserved.length ≤ 7*badPhaseCount (initialPhaseTests κ) C.phases ∧
        ENNReal.ofReal (Real.exp (-initialCutProductConstant*
          (((s.trackedPhases.flatMap (refinePhase choose)).length : ℝ)/Real.log B+
            μ*Scalar.SignedIntervals.positiveMass C.unselected+
            (badPhaseCount (initialPhaseTests κ) C.phases : ℝ)*(1+Real.log (κ/B))))*
          (cutReferenceProduct μ P (s.trackedPhases.flatMap (refinePhase choose)))^2) ≤ D κ C.word := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_initial_cut_numerical_bound] with A hA hbound
  intro κ B P C choose hAB hB hBκ hκA hκ hPL hPU hpiv hunselected hselected hnotselected
  obtain ⟨μ,s,hμ,hμu,hcritical,hcharge,hph,hs,hc,hreserved,hactual⟩ :=
    hbound κ B P C choose hAB hB hBκ hκA hκ hPL hPU hpiv hunselected hselected hnotselected
  have hA0 := zero_lt_one.trans hA
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hκ0 := zero_lt_one.trans_le hκ
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hlogA := Real.log_pos hA
  have hlogB := Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hB)
  have hlog : Real.log B ≤ 2*Real.log A := by
    have hh := Real.log_le_log hB0 ((by linarith only [hBκ,hκ0] : B ≤ κ).trans hκA)
    rw [Real.log_rpow hA0] at hh
    linarith only [hh,hlogA]
  let k := ((s.trackedPhases.flatMap (refinePhase choose)).length : ℝ)
  let X := k/Real.log B
  let Y := μ*Scalar.SignedIntervals.positiveMass C.unselected
  let Z := (badPhaseCount (initialPhaseTests κ) C.phases : ℝ)*(1+Real.log (κ/B))
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hcompare : k/Real.log A ≤ 2*(k/Real.log B) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hlogA hlogB).mpr
    have hh := mul_le_mul_of_nonneg_left hlog hk0
    nlinarith only [hh]
  have hscale := mul_le_mul_of_nonneg_left hcompare (by norm_num : (0 : ℝ) ≤ 2400)
  have hX0 : 0 ≤ X := div_nonneg hk0 hlogB.le
  have hY0 : 0 ≤ Y := mul_nonneg hμ0.le (Scalar.SignedIntervals.positiveMass_nonneg _)
  have hZ0 : 0 ≤ Z := by
    have hK : 1 ≤ κ/B := (one_le_div hB0).mpr (by linarith only [hBκ,hκ0])
    have hh := Real.log_nonneg hK
    dsimp only [Z]
    positivity
  have hb := initialCutProductConstant_bounds
  have hX := mul_le_mul_of_nonneg_right hb.2.1 hX0
  have hY := mul_le_mul_of_nonneg_right hb.2.2.1 hY0
  have hZ := mul_le_mul_of_nonneg_right hb.2.2.2 hZ0
  have hcost : initialNumericalCutLoss A κ B μ C s choose ≤ initialCutProductConstant*(X+Y+Z) := by
    change 2400*(k/Real.log A) ≤ 2400*(2*X) at hscale
    calc
      _ = 2400*(k/Real.log A)+6*Y+(7*(initialLogPriceConstant+6)+64)*Z := by
        dsimp only [initialNumericalCutLoss,k,Y,Z]
        ring
      _ ≤ _ := by nlinarith only [hscale,hX,hY,hZ]
  have he := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
    (sq_nonneg (cutReferenceProduct μ P (s.trackedPhases.flatMap (refinePhase choose))))
  refine ⟨μ,s,hμ,hμu,hcritical,hph,hreserved,?_⟩
  simpa only [X,Y,Z,k,neg_mul] using (ENNReal.ofReal_le_ofReal he).trans hactual

end
end StrongSilver
