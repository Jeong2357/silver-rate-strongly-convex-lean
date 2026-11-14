-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialPositiveTrace
import StrongSilver.InitialPositiveAttachment
import StrongSilver.SourceScaleRatio

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

theorem eventually_initial_gate_trace : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B : ℝ, ∀ h : List ℝ, InitialPhaseBudget A μ b T κ B h →
      ∀ s : List ℝ, ∀ η M G r : ℝ, PositiveTrace μ s η M G r → initialOldGate A κ B ≤ η →
      Nonempty (PositiveTrace μ ((h++[b])++s) (initialGateConstant/(κ/B)^2)
        (initialPointRelativeConstant*(κ/B)) (initialSlopeRelativeConstant*(κ/B)/κ)
        (r/(initialEntryConstant*(κ/B)^4))) := by
  filter_upwards [eventually_initial_positive_attachment] with A hattach
  intro μ b T κ B h W s η M G r S hη
  obtain ⟨n,J,hsteps,hend,hNZ,hpositive,hgate,hN,hprojections⟩ := hattach μ b T κ B h W
    (Space S.dimension) S.length S.path S.nonzero S.positive η S.gate hη
  have hK : 0 < κ/B := div_pos W.kappa_positive W.B_positive
  have hC : 0 < initialEntryConstant*(κ/B)^4 := mul_pos initialEntryConstant_positive (pow_pos hK 4)
  have hEndNorm : ‖J.x (Fin.last n)‖ = ‖S.path.x (Fin.last S.length)‖ := by
    calc
      _ = ‖retainedMap (W := PhaseSpace) (S.path.x (Fin.last S.length))‖ := congrArg norm hend
      _ = _ := retainedIsometry.norm_map _
  have hactual := ratio_lower_of_source_squared_scale (norm_pos_iff.mpr S.nonzero) (norm_pos_iff.mpr hNZ) hC
    (norm_nonneg (S.path.x (Fin.last S.length))) hEndNorm.symm.le hN
  have hratio := (div_le_div_of_nonneg_right S.ratio hC.le).trans hactual
  have hstepseq := hsteps.trans (congrArg (fun l : List ℝ => (h++[b])++l) S.steps_eq)
  exact ⟨PositiveTrace.ofInitialPath J hstepseq hNZ hpositive hgate hprojections hratio⟩

end
end StrongSilver
