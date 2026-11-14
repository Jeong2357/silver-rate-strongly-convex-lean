-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrdinaryRootSuffix
import StrongSilver.FourPhaseTrace
import StrongSilver.FiniteSourceProjectionCaps
import StrongSilver.OrdinaryReferenceFactor

namespace StrongSilver
open Real Filter Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3000000

/-- Actual right-gap ordinary attachment as a finite Euclidean retained
trace for the balanced depth construction. The height offset tends to
zero at an explicit negative power of A; the local certificate is kept
for the sharp planar scale estimates. -/
theorem eventually_ordinary_root_trace : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P h →
    ∀ i : Fin h.length, A^((499:ℝ)/500) ≤ h.get i → negativeMass h ≤ h.get i/16 →
    ∀ s : List ℝ, ∀ Mo Go r : ℝ, PositiveTrace μ s (workingGateFraction A) Mo Go r →
    ∃ e > 0, ∃ L : LocalPhaseCertificate A μ b T e h, ∃ M G : ℝ,
      e^2 = A^(-(3:ℝ)/25)*T*(‖L.R‖+P) ∧
      (L.sourceHeightOffset+‖L.R‖*(workingGateFraction A*L.sourceSlopeCap))/‖L.path.x 0‖^2 ≤ A^(-(1:ℝ)/20) ∧
      Nonempty (FourPhaseTrace μ ((h++[b])++s) (‖L.R‖/8)
        ((L.sourceHeightOffset+‖L.R‖*(workingGateFraction A*L.sourceSlopeCap))/‖L.path.x 0‖^2)
        (workingGateFraction A) M G (r*(ordinaryReferenceFactor A μ b P h)^2)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ordinary_root_suffix] with A hA hattach
  intro μ b T P h W i hroot hnegative s Mo Go r Q
  obtain ⟨e,he,L,n,J,heq,hword,hsource,hend,hB,hZ,hgate,hgain,hratio⟩ :=
    hattach μ b T P h W i hroot hnegative (Space Q.dimension) Q.length Q.path Q.nonzero Q.positive Q.gate
  obtain ⟨M,G,hprojections⟩ := finite_source_projection_caps J.family.z J.family.g hB.source_nonzero
  have hfac := W.reference_factor_positive hA
  change ordinaryReferenceFactor A μ b P h ≤ ‖L.path.x (Fin.last _)‖/‖L.path.x 0‖ at hgain
  have hsquared := (sq_le_sq₀ hfac.le (div_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hgain
  rw [div_pow] at hsquared
  have hmul := mul_le_mul Q.ratio hsquared (sq_nonneg (ordinaryReferenceFactor A μ b P h))
    (div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hrate : r*(ordinaryReferenceFactor A μ b P h)^2 ≤ ‖J.x (Fin.last n)‖^2/‖J.x 0‖^2 := by
    rw [hratio]
    exact hmul
  refine ⟨e,he,L,M,G,heq,hZ,?_⟩
  exact ⟨FourPhaseTrace.ofPath J (by simpa only [Q.steps_eq] using hword) hB hgate hprojections hrate⟩

end
end StrongSilver
