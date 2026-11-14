-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseCompleteLocalPath
import StrongSilver.FourPhaseLocalBudget
import StrongSilver.FourPhaseLocalInvariants
import StrongSilver.FourPhaseFiniteAttachment
import StrongSilver.FourPhaseLocalRelativeBounds
import StrongSilver.FourPhaseJointRelative

namespace StrongSilver.FourPhase.LocalParameters
open Scalar.SignedIntervals
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [ProperSpace (AttachmentSpace V Coordinates)]
set_option maxHeartbeats 3200000

/-- Actual four-phase schedule attachment, with retained contact values
and slopes in a common family. All local query budgets are paid by the
original negative steps. -/
theorem exists_supported_attachment (D : LocalParameters) (J : JoiningScaleConditions D)
    {m : ℕ} (Q : SupportedPath V D.μ m) {H Z η : ℝ}
    (B : FourPhaseSuffixBounds Q.family (Q.x 0) H Z)
    (hH : H ≤ D.T*lastExcess D.μ D.T D.gap D.pivot/2)
    (hZ : 2*lastExcess D.μ D.T D.gap D.pivot*Z ≤ D.ζ)
    (hN : ∀ i : Fin 3, 1000*lastExcess D.μ D.T D.gap D.pivot*negativeMass (D.gap i.castSucc) ≤ H)
    (hη : 0 ≤ η) (hηζ : 512*η ≤ D.ζ) :
    ∃ F : SupportFamily (D.QueryIndex ⊕ Fin m) (AttachmentSpace V Coordinates),
    ∃ n : ℕ, ∃ P : SupportedPath (AttachmentSpace V Coordinates) D.μ n,
      List.ofFn P.steps = D.totalWord++List.ofFn Q.steps ∧
      P.x 0 = axisAttachment (Q.x 0) D.joiningScale (source D.shape) ∧
      P.x (Fin.last n) = retainedMap (W := Coordinates) (Q.x (Fin.last m)) ∧
      FourPhaseSuffixBounds P.family (P.x 0) D.T 0 ∧ P.family.Gate (P.x 0) η ∧
      P.WithinFamily F ∧
      (∀ j, F.z (Sum.inr j) = retainedMap (W := Coordinates) (Q.family.z j) ∧
        F.g (Sum.inr j) = retainedMap (W := Coordinates) (Q.family.g j) ∧ F.d (Sum.inr j) = Q.family.d j) ∧
      (∀ i, |inner ℝ (unitDirection (P.x 0)) (P.family.z i)| ≤ 26*‖P.x 0‖ ∧
        |inner ℝ (unitDirection (P.x 0)) (P.family.g i)| ≤ (1/D.T)*‖P.x 0‖) := by
  have hK := D.joiningScale_bounds J
  have hk : 0 < lastExcess D.μ D.T D.gap D.pivot := by linarith only [J.last_excess_lower]
  have hslope := retained_slope_margin D.geometry.a_upper D.geometry.regular.a_positive.le
    B.scale_positive.le D.time_positive.le hk.le hH hK.2.1
  have hoff := retained_offset_margin hK.2.2.1 hk.le B.offset_nonnegative hZ
  obtain ⟨F,hFB,hFG,hnew,hold⟩ := attach_four_phase_families D.geometry.regular B D.time_positive hK.1
    D.offset_nonnegative hoff hslope D.localFamily (fun j : D.QueryIndex => j.1)
    (fun _ => rfl) (fun _ => rfl) D.localFamily_renewal (D.localFamily_gate hη hηζ)
    (D.local_retained_budget J B.scale_positive hN)
  obtain ⟨n₀,P₀,hword,hsource,hend,hrows⟩ := D.exists_complete_local_path
  let A := axisAttachment (Q.x 0) D.joiningScale
  let c := (‖Q.x 0‖/D.joiningScale)^2
  have hc : 0 ≤ c := sq_nonneg _
  have hA : ∀ z g, inner ℝ (A z) (A g) = c*inner ℝ z g := axisAttachment_inner B.source_nonzero _
  let PP := P₀.transport A c hc hA
  let QQ := Q.transport (retainedMap (W := Coordinates)) 1 zero_le_one (fun z g => by rw [retained_inner,one_mul])
  have hPP : PP.WithinFamily F := by
    intro i
    obtain ⟨j,hz,hg,hd⟩ := hrows i
    refine ⟨Sum.inl j,?_,?_,?_⟩
    · change A (P₀.family.z i) = F.z (Sum.inl j)
      rw [hz,(hnew j).1]
    · change A (P₀.family.g i) = F.g (Sum.inl j)
      rw [hg,(hnew j).2.1]
    · change c*P₀.family.d i = F.d (Sum.inl j)
      rw [hd,(hnew j).2.2]
  have hQQ : QQ.WithinFamily F := by
    intro j
    refine ⟨Sum.inr j,?_,?_,?_⟩
    · exact (hold j).1.symm
    · exact (hold j).2.1.symm
    · change 1*Q.family.d j = F.d (Sum.inr j)
      rw [(hold j).2.2,one_mul]
  have hjoin : PP.x (Fin.last n₀) = QQ.x 0 := by
    change A (P₀.x (Fin.last n₀)) = retainedMap (W := Coordinates) (Q.x 0)
    rw [hend]
    exact axisAttachment_endpoint B.source_nonzero hK.1.ne'
  obtain ⟨P,hPs,hPe,hPw,hPr⟩ := PP.concat_within_family QQ F hPP hQQ hjoin
  have hstart : P.x 0 = A (source D.shape) := hPs.trans (congrArg A hsource)
  refine ⟨F,_,P,?_,hstart,hPe,?_,?_,hPr,hold,?_⟩
  · rw [hPw]
    change List.ofFn P₀.steps++List.ofFn Q.steps = _
    rw [hword]
  · rw [hstart]
    exact hFB.of_rows hPr
  · rw [hstart]
    exact F.gate_of_rows P.family hFG hPr
  · have hlocalabs (j : D.QueryIndex) :
        |inner ℝ (source D.shape) (D.localFamily.z j)| ≤ 26*‖source D.shape‖^2 ∧
        |inner ℝ (source D.shape) (D.localFamily.g j)| ≤ (1/D.T)*‖source D.shape‖^2 := by
      have hbounds := D.localFamily_relative_inner_bounds J hH hN j
      have hpositive := D.localFamily_renewal
      rw [abs_of_nonneg (hpositive.point_positive j),abs_of_nonneg (hpositive.slope_positive j)]
      exact hbounds
    have hcaps := joint_source_caps B.source_nonzero (source_orthogonal_axis D.geometry.regular)
      (by norm_num : (0:ℝ) ≤ 26) (one_div_pos.mpr D.time_positive).le hlocalabs
      (fun j => ⟨(hnew j).1,(hnew j).2.1⟩) (fun j => ⟨(hold j).1,(hold j).2.1⟩)
    intro i
    obtain ⟨j,hz,hg,hd⟩ := hPr i
    rw [hstart,hz,hg]
    exact unit_relative_of_quadratic hFB.source_nonzero (hcaps j).1 (hcaps j).2

end
end StrongSilver.FourPhase.LocalParameters
