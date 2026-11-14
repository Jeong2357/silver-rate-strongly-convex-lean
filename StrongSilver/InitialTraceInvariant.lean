-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TraceInitialSupply
import StrongSilver.InitialGateComparisons
import StrongSilver.EventualUniformTail

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1600000

/-- The native initial-block invariant uniformly supplies the working
invariant used by tracked phases at every permitted refined cutoff. -/
theorem eventually_initial_trace_to_working : ∀ᶠ A : ℝ in atTop,
    ∀ κ K μ r : ℝ, ∀ h : List ℝ, 1 ≤ κ → 0 < K → K ≤ A^((3 : ℝ)/1000) →
      PositiveTrace μ h (initialGateConstant/K^2) (initialPointRelativeConstant*K)
        (initialSlopeRelativeConstant*K/κ) r →
      Nonempty (PositiveTrace μ h (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ)) r) := by
  filter_upwards [eventually_initial_gate_covers_working,
    eventually_const_mul_power_le (by norm_num : (3 : ℝ)/1000 < 10) initialPointRelativeConstant,
    eventually_const_mul_power_le (by norm_num : (3 : ℝ)/1000 < 10) initialSlopeRelativeConstant]
    with A hgate hpoint hslope
  intro κ K μ r h hκ hK hKA S
  have hM := (mul_le_mul_of_nonneg_left hKA initialPointRelativeConstant_positive.le).trans hpoint
  have hG : initialSlopeRelativeConstant*K/κ ≤ A^(10 : ℝ) := by
    have hX : 0 ≤ initialSlopeRelativeConstant*K := mul_nonneg initialSlopeRelativeConstant_positive.le hK.le
    have hdiv : initialSlopeRelativeConstant*K/κ ≤ initialSlopeRelativeConstant*K := by
      apply (div_le_iff₀ (zero_lt_one.trans_le hκ)).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hκ hX
    exact hdiv.trans ((mul_le_mul_of_nonneg_left hKA initialSlopeRelativeConstant_positive.le).trans hslope)
  exact ⟨S.weaken (hgate K hK hKA) hM hG le_rfl⟩

theorem eventually_initial_old_gate_below_working : ∀ᶠ A : ℝ in atTop,
    ∀ κ B : ℝ, 0 ≤ κ → κ ≤ A^((1003 : ℝ)/1000) → A ≤ B →
      initialOldGate B κ B ≤ workingGateFraction A := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_all_larger eventually_initial_old_gate_small]
    with A hA hold
  intro κ B hκ hκA hAB
  have hA0 := zero_lt_one.trans hA
  have hκB : κ ≤ B^((1003 : ℝ)/1000) :=
    hκA.trans (Real.rpow_le_rpow hA0.le hAB (by norm_num))
  have hB := hold B hAB κ B hκ hκB le_rfl
  apply hB.trans
  exact (Real.rpow_le_rpow_of_nonpos hA0 hAB (by norm_num : -(19 : ℝ)/100 ≤ 0)).trans
    (Real.rpow_le_rpow_of_exponent_le hA.le (by norm_num : -(19 : ℝ)/100 ≤ -(67 : ℝ)/500))

/-- A reserved gate-supplying phase is built at the original cutoff B;
the retained positive suffix may be built at any refined cutoff A≤B. -/
theorem eventually_initial_gate_from_working : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ b T : ℝ, ∀ h : List ℝ,
      A ≤ B → κ ≤ A^((1003 : ℝ)/1000) → InitialPhaseBudget B μ b T κ B h →
      ∀ s : List ℝ, ∀ M G r : ℝ,
      PositiveTrace μ s (workingGateFraction A) M G r →
      Nonempty (PositiveTrace μ ((h++[b])++s) (initialGateConstant/(κ/B)^2)
        (initialPointRelativeConstant*(κ/B)) (initialSlopeRelativeConstant*(κ/B)/κ)
        (r/(initialEntryConstant*(κ/B)^4))) := by
  filter_upwards [eventually_initial_old_gate_below_working,eventually_all_larger eventually_initial_gate_trace]
    with A hgate hattach
  intro κ B μ b T h hAB hκA W s M G r S
  exact hattach B hAB μ b T κ B h W s (workingGateFraction A) M G r S (hgate κ B W.kappa_positive.le hκA hAB)

end
end StrongSilver
