-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialMarkedCount

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2600000

def initialNumericalCutLoss (A κ B μ : ℝ) (C : ScheduleCut) (s : CompleteInitialCutAssembly)
    (choose : ℕ → ℝ → Bool) : ℝ :=
  2400*((s.trackedPhases.flatMap (refinePhase choose)).length : ℝ)/Real.log A+
  6*μ*Scalar.SignedIntervals.positiveMass C.unselected+
  (7*(initialLogPriceConstant+6)+64)*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ)*(1+Real.log (κ/B))

/-- Initial-cut bound with the original numerical marked count. One
curvature is chosen in the proof, avoids every root, and pays the large-step
inverse charge from that same marked count. -/
theorem eventually_initial_cut_numerical_bound : ∀ᶠ A : ℝ in atTop,
    ∀ κ B P : ℝ, ∀ C : ScheduleCut, ∀ choose : ℕ → ℝ → Bool,
      A ≤ B → 2 ≤ B → B ≤ κ/4 → κ ≤ A^((1003 : ℝ)/1000) → 1 ≤ κ →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ q ∈ C.phases, B ≤ q.pivot) → (∀ b ∈ C.unselected, 0 < b → b ≤ B) →
      (∀ i b, choose i b = true → A ≤ b) → (∀ i b, choose i b = false → 0 < b → b ≤ A) →
      ∃ μ : ℝ, ∃ s : CompleteInitialCutAssembly,
        1/κ ≤ μ ∧ μ ≤ 9/(8*κ) ∧ (∀ b ∈ C.word, 1-μ*b ≠ 0) ∧
        largeInverseCharge κ C.word μ ≤ 32*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ) ∧
        s.phases = C.phases ∧ s.WellFormed (initialMarkedGood κ B μ) ∧ s.Counted (initialMarkedGood κ B μ) ∧
        s.reserved.length ≤ 7*badPhaseCount (initialPhaseTests κ) C.phases ∧
        ENNReal.ofReal (Real.exp (-initialNumericalCutLoss A κ B μ C s choose)*
          (cutReferenceProduct μ P (s.trackedPhases.flatMap (refinePhase choose)))^2) ≤ D κ C.word := by
  filter_upwards [eventually_initial_cut_distance_bound] with A hlower
  intro κ B P C choose hAB hB hBκ hκA hκ hPL hPU hpiv hunselected hselected hnotselected
  have hκ0 := zero_lt_one.trans_le hκ
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hBκ' : B ≤ κ := by linarith only [hBκ,hκ0]
  have hBhalf : B < κ/2 := by linarith only [hBκ,hκ0]
  obtain ⟨μ,hμ,hμu,hcritical,hcharge⟩ := exists_common_curvature_strict hκ0 C.word
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hμκ : μ*κ ≤ 9/8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*κ)).mp hμu
    nlinarith only [hh]
  have hcap : μ*B ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left hBκ hμ0.le
    nlinarith only [hh,hμκ]
  have hgap : ∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ B :=
    fun q hq b hb hb0 => hunselected b (ScheduleCut.mem_gap_unselected hq hb) hb0
  have ht : ∀ b ∈ C.terminal, 0 < b → b ≤ B :=
    fun b hb hb0 => hunselected b (ScheduleCut.mem_terminal_unselected hb) hb0
  have hJ := initial_marked_count_le hκ hB0 hBκ hμ hμu C.phases hpiv hgap
  have hcount := C.strictLarge_le_initial_marked hκ0 hBhalf hunselected
  have hcountReal : ((strictLargeSteps κ C.word).length : ℝ) ≤ (badPhaseCount (initialPhaseTests κ) C.phases : ℝ) := by exact_mod_cast hcount
  have hcharge' : largeInverseCharge κ C.word μ ≤ 32*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ) := by linarith only [hcharge,hcountReal]
  obtain ⟨s,hph,hs,hc,hreserved,hactual⟩ := hlower κ B μ (3*κ/4) P (initialMarkedGood κ B μ)
    (fun _ hq => initialMarkedGood_budget hq) C choose hAB hB hBκ' hκA hκ hμ hμu hcap hPL hPU
    hselected hnotselected hgap ht hcritical
  have hword : s.word C.terminal = C.word := by simp only [CompleteInitialCutAssembly.word,hph,ScheduleCut.word]
  have hmass := C.unselected_positiveMass
  change Scalar.SignedIntervals.positiveMass C.unselected = phaseGapMass C.phases+Scalar.SignedIntervals.positiveMass C.terminal at hmass
  have hJreal : (badPhaseCount (initialMarkedGood κ B μ) C.phases : ℝ) ≤ (badPhaseCount (initialPhaseTests κ) C.phases : ℝ) := by exact_mod_cast hJ
  have hL : 1 ≤ 1+Real.log (κ/B) := by have hh := Real.log_nonneg ((one_le_div hB0).mpr hBκ'); linarith only [hh]
  have hCoefficient : 0 ≤ 7*(initialLogPriceConstant+6) := by have hh := initialLogPriceConstant_positive; positivity
  have hJprice := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJreal hCoefficient) (zero_le_one.trans hL)
  have hRprice : 64*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ) ≤
      64*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ)*(1+Real.log (κ/B)) := by
    have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ 64*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ) by positivity)
    simpa only [mul_one] using hh
  have hcost : initialCutLoss A κ B μ (initialMarkedGood κ B μ) s choose C.terminal ≤ initialNumericalCutLoss A κ B μ C s choose := by
    unfold initialCutLoss initialNumericalCutLoss
    rw [hph,hword,← hmass]
    nlinarith only [hJprice,hRprice,hcharge']
  have he := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
    (sq_nonneg (cutReferenceProduct μ P (s.trackedPhases.flatMap (refinePhase choose))))
  refine ⟨μ,s,hμ,hμu,hcritical,hcharge',hph,hs,hc,?_,(ENNReal.ofReal_le_ofReal he).trans hactual⟩
  exact hreserved.trans (Nat.mul_le_mul_left 7 hJ)

end
end StrongSilver
