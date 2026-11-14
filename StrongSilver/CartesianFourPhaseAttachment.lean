-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseFiniteLemma
import StrongSilver.FourPhaseGainTransfer
import StrongSilver.CartesianGroupMassShape

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

/-- The actual four-phase attachment expressed using exact Cartesian
log gains and the exact exterior leading factor. The finite comparison
errors are explicit, so they can be summed across all depth groups. -/
theorem finite_tree_gain_attachment : ∃ C > 0, ∃ ε₀ > 0, ∃ c₀ > 0,
    ∀ S : PhaseSchedule, ∀ G : FourGapGroup, ∀ φ : ℝ → ℝ,
    ∀ ε eG eM eK K : ℝ, 0 ≤ ε → ε ≤ ε₀ → 0 < K →
    (∀ i : Fin 8, i ≠ 7 → |S.shape 0 i-reference i| ≤ ε) →
    0 < totalMass (S.shape 0) →
    (|gain (S.shape 0)-rootGain φ G.tree|+|gainLeft (S.shape 0)-rootGain φ G.left|+
      |gainRight (S.shape 0)-rootGain φ G.right| ≤ eG) →
    |Real.log (totalMass (S.shape 0))-Real.log (G.tree.prefixMass φ/S.T)| ≤ eM →
    |Real.log (S.T*S.k/K)| ≤ eK →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [ProperSpace (AttachmentSpace V Coordinates)],
    ∀ m : ℕ, ∀ Q : SupportedPath V S.μ m, ∀ H Z η : ℝ,
    FourPhaseSuffixBounds Q.family (Q.x 0) H Z → H ≤ S.T*S.k/2 → S.k*Z ≤ c₀ →
    (∀ i : Fin 3, negativeMass (S.gap i.castSucc) ≤ c₀*H/S.k) →
    0 ≤ η → η ≤ c₀ →
    ∃ F : SupportFamily (S.LocalQueryIndex ⊕ Fin m) (AttachmentSpace V Coordinates),
    ∃ n : ℕ, ∃ P : SupportedPath (AttachmentSpace V Coordinates) S.μ n,
      List.ofFn P.steps = S.totalWord++List.ofFn Q.steps ∧
      P.x (Fin.last n) = retainedMap (W := Coordinates) (Q.x (Fin.last m)) ∧
      FourPhaseSuffixBounds P.family (P.x 0) S.T 0 ∧ P.family.Gate (P.x 0) η ∧
      P.WithinFamily F ∧
      (∀ j, F.z (Sum.inr j) = retainedMap (W := Coordinates) (Q.family.z j) ∧
        F.g (Sum.inr j) = retainedMap (W := Coordinates) (Q.family.g j) ∧ F.d (Sum.inr j) = Q.family.d j) ∧
      (∀ i, |inner ℝ (unitDirection (P.x 0)) (P.family.z i)| ≤ 26*‖P.x 0‖ ∧
        |inner ℝ (unitDirection (P.x 0)) (P.family.g i)| ≤ (1/S.T)*‖P.x 0‖) ∧
      signedThreeGain (rootGain φ G.tree) (rootGain φ G.left) (rootGain φ G.right)-
        C*ε*(|rootGain φ G.tree|+|rootGain φ G.left|+|rootGain φ G.right|)-
        (C+2)*eG-C*(η+S.k*Z)-2*(eK+eM) ≤
      Real.log ((‖Q.x 0‖^2/‖P.x 0‖^2)*(G.tree.prefixMass φ/K)^2) := by
  obtain ⟨C,hC,d,hd,c,hc,hattach⟩ := finite_four_phase_attachment
  refine ⟨C,hC,min d 1,lt_min hd (by norm_num),c,hc,?_⟩
  intro S G φ ε eG eM eK K hε hεδ hK hnear htotal hG hM hKlog V _ _ _ m Q H Z η B hH hZ hN hη hηc
  obtain ⟨F,n,P,hword,hsource,hend,hB,hgate,hwithin,hold,hrel,hgain⟩ :=
    hattach S ε hε (hεδ.trans (min_le_left _ _)) hnear V m Q H Z η B hH hZ hN hη hηc
  simp only [PhaseSchedule.shape,gain_productShape_offset,gainLeft_productShape_offset,
    gainRight_productShape_offset,totalMass_productShape_offset] at hgain
  change signedThreeGain (gain (S.shape 0)) (gainLeft (S.shape 0)) (gainRight (S.shape 0))-
    C*ε*(|gain (S.shape 0)|+|gainLeft (S.shape 0)|+|gainRight (S.shape 0)|)-C*(η+S.k*Z) ≤
    Real.log ((‖Q.x 0‖^2/‖P.x 0‖^2)*(totalMass (S.shape 0)/S.k)^2) at hgain
  have htree := three_gain_lower_transfer hC.le hε (hεδ.trans (min_le_right _ _)) hG hgain
  have hr : 0 < ‖Q.x 0‖^2/‖P.x 0‖^2 := div_pos
    (sq_pos_of_pos (norm_pos_iff.mpr B.source_nonzero)) (sq_pos_of_pos (norm_pos_iff.mpr hB.source_nonzero))
  have hm : 0 < G.tree.prefixMass φ/S.T := div_pos (prefixMass_positive φ G.tree) S.time_positive
  have hnorm := log_normalization_error hr htotal hm S.k_positive S.time_positive hK hKlog hM
  have hcancel : S.T*(G.tree.prefixMass φ/S.T) = G.tree.prefixMass φ := by
    field_simp [S.time_positive.ne']
  rw [hcancel] at hnorm
  exact ⟨F,n,P,hword,hend,hB,hgate,hwithin,hold,hrel,by linarith only [htree,hnorm]⟩

end
end StrongSilver.ScheduleTree.FourGapGroup
