-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialTraceInvariant
import StrongSilver.TraceExceptional
import StrongSilver.TraceTerminalBases

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

theorem initial_ratio_at_refined_cut {A κ B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hκ : κ ≤ A^((1003 : ℝ)/1000)) : κ/B ≤ A^((3 : ℝ)/1000) := by
  calc
    _ ≤ A^((1003 : ℝ)/1000)/B := div_le_div_of_nonneg_right hκ (hA.le.trans hAB)
    _ ≤ A^((1003 : ℝ)/1000)/A := div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hA _).le hA hAB
    _ = A^((1003 : ℝ)/1000)/A^(1 : ℝ) := by rw [Real.rpow_one]
    _ = A^((1003 : ℝ)/1000-1) := (Real.rpow_sub hA _ _).symm
    _ = _ := by congr 1; norm_num

def initialReservedRate (κ B μ : ℝ) (I : List ℝ) (r : ℝ) : ℝ :=
  (r/(initialEntryConstant*(κ/B)^4))/(initialBlockFactor κ B μ I)^2

/-- A reserved initial block includes its gate-supplying phase on the right.
The native initial invariant is converted back to the refined working
invariant after the block, with a price polynomial in kappa/B. -/
theorem eventually_initial_reserved_trace : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ b T c d U : ℝ, ∀ h I g : List ℝ,
      A ≤ B → κ ≤ A^((1003 : ℝ)/1000) →
      InitialPhaseBudget B μ b T κ B h → InitialPhaseBudget B μ d U κ B g →
      2 ≤ c → B ≤ c → c ≤ κ → 1/32 ≤ 1-μ*c → (∀ a ∈ I, 1-μ*a ≠ 0) →
      ∀ s : List ℝ, ∀ M G r : ℝ, PositiveTrace μ s (workingGateFraction A) M G r →
      Nonempty (PositiveTrace μ ((h++[b])++((I++[c])++((g++[d])++s)))
        (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ)) (initialReservedRate κ B μ I r)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_initial_gate_from_working,
    eventually_all_larger eventually_initial_exceptional_trace,eventually_initial_trace_to_working]
    with A hA hgate hblock hworking
  intro κ B μ b T c d U h I g hAB hκA W Wg hc hcB hcκ hqc hcritical s M G r S
  obtain ⟨Sg⟩ := hgate κ B μ d U g hAB hκA Wg s M G r S
  obtain ⟨Sb⟩ := hblock B hAB μ b T κ B c h I W hc hcB hcκ hqc hcritical ((g++[d])++s) _ Sg
  exact hworking κ (κ/B) μ _ _ W.kappa_large (div_pos W.kappa_positive W.B_positive)
    (initial_ratio_at_refined_cut hA hAB hκA) Sb

theorem eventually_initial_terminal_working_trace : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ b T c : ℝ, ∀ h I t : List ℝ,
      A ≤ B → κ ≤ A^((1003 : ℝ)/1000) → InitialPhaseBudget B μ b T κ B h →
      2 ≤ c → B ≤ c → 1/32 ≤ 1-μ*c → μ*B ≤ 1/2 →
      (∀ a ∈ I, 1-μ*a ≠ 0) → (∀ a ∈ t, 0 < a → a ≤ B) →
      Nonempty (PositiveTrace μ ((h++[b])++((I++[c])++t))
        (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ)) (initialTerminalRate κ B μ I t)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_all_larger eventually_initial_terminal_trace,
    eventually_initial_trace_to_working] with A hA hterminal hworking
  intro κ B μ b T c h I t hAB hκA W hc hcB hqc hcap hcritical ht
  obtain ⟨S⟩ := hterminal B hAB μ b T κ B c h I t W hc hcB hqc hcap hcritical ht
  exact hworking κ (κ/B) μ _ _ W.kappa_large (div_pos W.kappa_positive W.B_positive)
    (initial_ratio_at_refined_cut hA hAB hκA) S

theorem eventually_initial_no_connector_working_trace : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ b T : ℝ, ∀ h I t : List ℝ,
      A ≤ B → κ ≤ A^((1003 : ℝ)/1000) → InitialPhaseBudget B μ b T κ B h → μ*B ≤ 1/2 →
      (∀ a ∈ I, 1-μ*a ≠ 0) → (∀ a ∈ t, 0 < a → a ≤ B) →
      Nonempty (PositiveTrace μ ((h++[b])++(I++t))
        (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ)) (initialNoConnectorRate κ B μ I t)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_all_larger eventually_initial_no_connector_trace,
    eventually_initial_trace_to_working] with A hA hterminal hworking
  intro κ B μ b T h I t hAB hκA W hcap hcritical ht
  obtain ⟨S⟩ := hterminal B hAB μ b T κ B h I t W hcap hcritical ht
  exact hworking κ (κ/B) μ _ _ W.kappa_large (div_pos W.kappa_positive W.B_positive)
    (initial_ratio_at_refined_cut hA hAB hκA) S

end
end StrongSilver
