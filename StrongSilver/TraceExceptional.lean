-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PositiveTrace
import StrongSilver.WorkingExceptionalAttachment
import StrongSilver.InitialExceptionalAttachment
import StrongSilver.SourceScaleRatio

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

def workingBlockFactor (A μ : ℝ) (I : List ℝ) : ℝ :=
  A^(25 : ℝ)*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I)
def initialBlockFactor (κ B μ : ℝ) (I : List ℝ) : ℝ :=
  initialBlockConstant*(κ/B)^6*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ)

theorem eventually_working_exceptional_trace : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P c : ℝ, ∀ h I : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      2 ≤ c → c ≤ A^(2 : ℝ) → 1/32 ≤ 1-μ*c → (∀ a ∈ I, 1-μ*a ≠ 0) →
      ∀ s : List ℝ, ∀ r : ℝ,
      PositiveTrace μ s (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ)) r →
      Nonempty (PositiveTrace μ ((h++[b])++((I++[c])++s)) (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ))
        (r/(workingBlockFactor A μ I)^2)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_working_exceptional_attachment] with A hA hattach
  intro μ b T P c h I W hc hcA hqc hcritical s r S
  have hη : 0 < workingGateFraction A := Real.rpow_pos_of_pos hA _
  have hminus : S.path.family.Gate (S.path.x 0) (-workingGateFraction A) :=
    S.path.family.gate_below S.positive.2 S.gate (by linarith only [hη])
  obtain ⟨n,J,hsteps,hend,hNZ,hpositive,hgate,hprojections,hN⟩ := hattach μ b T P c h I W hc hcA hqc hcritical
    (Space S.dimension) S.length S.path S.nonzero S.gate hminus S.projections
  have hC : 0 < workingBlockFactor A μ I := by
    have hS := smallPositiveSum_nonneg μ I
    unfold workingBlockFactor
    positivity
  have hNfactor : ‖J.x 0‖ ≤ workingBlockFactor A μ I*‖S.path.x 0‖ := by
    apply hN.trans_eq
    unfold workingBlockFactor
    ring
  have hEndNorm : ‖J.x (Fin.last n)‖ = ‖S.path.x (Fin.last S.length)‖ := by
    calc
      _ = ‖retainedMap (W := PhaseSpace) (retainedMap (W := ℂ) (S.path.x (Fin.last S.length)))‖ := congrArg norm hend
      _ = ‖retainedMap (W := ℂ) (S.path.x (Fin.last S.length))‖ := retainedIsometry.norm_map _
      _ = _ := retainedIsometry.norm_map _
  have hactual := ratio_lower_of_source_scale (norm_pos_iff.mpr S.nonzero) (norm_pos_iff.mpr hNZ) hC
    (norm_nonneg (S.path.x (Fin.last S.length))) hEndNorm.symm.le hNfactor
  have hratio := (div_le_div_of_nonneg_right S.ratio (sq_nonneg (workingBlockFactor A μ I))).trans hactual
  have hstepseq := hsteps.trans (congrArg (fun l : List ℝ => (h++[b])++((I++[c])++l)) S.steps_eq)
  exact ⟨PositiveTrace.ofPath J hstepseq hNZ hpositive hgate hprojections hratio⟩

theorem eventually_initial_exceptional_trace : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B c : ℝ, ∀ h I : List ℝ, InitialPhaseBudget A μ b T κ B h →
      2 ≤ c → B ≤ c → c ≤ κ → 1/32 ≤ 1-μ*c → (∀ a ∈ I, 1-μ*a ≠ 0) →
      ∀ s : List ℝ, ∀ r : ℝ,
      PositiveTrace μ s (initialGateConstant/(κ/B)^2) (initialPointRelativeConstant*(κ/B))
        (initialSlopeRelativeConstant*(κ/B)/κ) r →
      Nonempty (PositiveTrace μ ((h++[b])++((I++[c])++s)) (initialGateConstant/(κ/B)^2)
        (initialPointRelativeConstant*(κ/B)) (initialSlopeRelativeConstant*(κ/B)/κ)
        (r/(initialBlockFactor κ B μ I)^2)) := by
  filter_upwards [eventually_initial_exceptional_attachment] with A hattach
  intro μ b T κ B c h I W hc hcB hcκ hqc hcritical s r S
  have hqueries (i) : |inner ℝ (unitDirection (S.path.x 0)) (S.path.family.z i)| ≤ initialPointRelativeConstant*(κ/B)*‖S.path.x 0‖ ∧
      |inner ℝ (unitDirection (S.path.x 0)) (S.path.family.g i)| ≤ initialSlopeRelativeConstant*(κ/B)*‖S.path.x 0‖/κ := by
    refine ⟨(S.projections i).1,(S.projections i).2.trans_eq ?_⟩
    ring
  obtain ⟨n,J,hsteps,hend,hNZ,hpositive,hgate,hprojections,hN⟩ := hattach μ b T κ B c h I W hc hcB hcκ hqc hcritical
    (Space S.dimension) S.length S.path S.nonzero S.positive S.gate hqueries
  have hK : 0 < κ/B := div_pos W.kappa_positive W.B_positive
  have hκ := W.kappa_positive
  have hC : 0 < initialBlockFactor κ B μ I := by
    have hS := smallPositiveSum_nonneg μ I
    have hC := initialBlockConstant_positive
    unfold initialBlockFactor
    positivity
  have hNfactor : ‖J.x 0‖ ≤ initialBlockFactor κ B μ I*‖S.path.x 0‖ := by
    apply hN.trans_eq
    unfold initialBlockFactor
    ring
  have hEndNorm : ‖J.x (Fin.last n)‖ = ‖S.path.x (Fin.last S.length)‖ := by
    calc
      _ = ‖retainedMap (W := PhaseSpace) (retainedMap (W := ℂ) (S.path.x (Fin.last S.length)))‖ := congrArg norm hend
      _ = ‖retainedMap (W := ℂ) (S.path.x (Fin.last S.length))‖ := retainedIsometry.norm_map _
      _ = _ := retainedIsometry.norm_map _
  have hactual := ratio_lower_of_source_scale (norm_pos_iff.mpr S.nonzero) (norm_pos_iff.mpr hNZ) hC
    (norm_nonneg (S.path.x (Fin.last S.length))) hEndNorm.symm.le hNfactor
  have hratio := (div_le_div_of_nonneg_right S.ratio (sq_nonneg (initialBlockFactor κ B μ I))).trans hactual
  have hstepseq := hsteps.trans (congrArg (fun l : List ℝ => (h++[b])++((I++[c])++l)) S.steps_eq)
  have hbounds (i) : |inner ℝ (unitDirection (J.x 0)) (J.family.z i)| ≤ (initialPointRelativeConstant*(κ/B))*‖J.x 0‖ ∧
      |inner ℝ (unitDirection (J.x 0)) (J.family.g i)| ≤ (initialSlopeRelativeConstant*(κ/B)/κ)*‖J.x 0‖ := by
    refine ⟨(hprojections i).1,(hprojections i).2.trans_eq ?_⟩
    ring
  exact ⟨PositiveTrace.ofPath J hstepseq hNZ hpositive hgate hbounds hratio⟩

end
end StrongSilver
