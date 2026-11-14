-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianNormalizedSchedule
import StrongSilver.CartesianFourPhaseAttachment

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 4800000

/-- A balanced original Cartesian group extends any retained suffix
satisfying (4.18), with its exact Cartesian gains and exterior factor.
All local interpolation data, product-time comparisons and logarithmic
normalizations are constructed from the original numerical data. -/
theorem balanced_group_attachment : ∃ C > 0, ∃ δ > 0, ∃ c > 0,
    ∀ G : FourGapGroup, ∀ μ T b ε B : ℝ,
    BalancedGroupData G μ T b ε → ε+μ*T ≤ δ → 0 ≤ B → μ*B ≤ 1/2 →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [ProperSpace (AttachmentSpace V Coordinates)],
    ∀ m : ℕ, ∀ Q : SupportedPath V μ m, ∀ H Z η : ℝ,
    FourPhaseSuffixBounds Q.family (Q.x 0) H Z →
    H ≤ T*lastExcess μ T G.gaps (G.pivots b)/2 →
    lastExcess μ T G.gaps (G.pivots b)*Z ≤ c →
    (∀ i : Fin 3, negativeMass (G.gaps i.castSucc) ≤ c*H/lastExcess μ T G.gaps (G.pivots b)) →
    0 ≤ η → η ≤ c →
    ∃ (ι : Type), ∃ _ : Fintype ι, ∃ F : SupportFamily ι (AttachmentSpace V Coordinates),
    ∃ keep : Fin m → ι,
    ∃ n : ℕ, ∃ P : SupportedPath (AttachmentSpace V Coordinates) μ n,
      List.ofFn P.steps = (G.tree.word++[b])++List.ofFn Q.steps ∧
      P.x (Fin.last n) = retainedMap (W := Coordinates) (Q.x (Fin.last m)) ∧
      FourPhaseSuffixBounds P.family (P.x 0) T 0 ∧ P.family.Gate (P.x 0) η ∧
      P.WithinFamily F ∧
      (∀ j, F.z (keep j) = retainedMap (W := Coordinates) (Q.family.z j) ∧
        F.g (keep j) = retainedMap (W := Coordinates) (Q.family.g j) ∧ F.d (keep j) = Q.family.d j) ∧
      (∀ i, |inner ℝ (unitDirection (P.x 0)) (P.family.z i)| ≤ 26*‖P.x 0‖ ∧
        |inner ℝ (unitDirection (P.x 0)) (P.family.g i)| ≤ (1/T)*‖P.x 0‖) ∧
      signedThreeGain (rootGain (logarithmicStep μ) G.tree)
        (rootGain (logarithmicStep μ) G.left) (rootGain (logarithmicStep μ) G.right)-
        C*(ε+μ*T)*(|rootGain (logarithmicStep μ) G.tree|+|rootGain (logarithmicStep μ) G.left|+
          |rootGain (logarithmicStep μ) G.right|)-
        C*(μ*T+μ*b+η+lastExcess μ T G.gaps (G.pivots b)*Z) ≤
      Real.log ((‖Q.x 0‖^2/‖P.x 0‖^2)*
        (G.tree.prefixMass (logarithmicStep μ)/(cappedStep μ B b-1-drawdown ((G.gaps 3).map (logarithmicStep μ))))^2) := by
  obtain ⟨Cs,hCs,ds,hds,hschedule⟩ := exists_normalized_group_schedule
  obtain ⟨Ca,hCa,da,hda,c,hc,hattach⟩ := finite_tree_gain_attachment
  let C := Ca*Cs+(Ca+4)*Cs+Ca+41
  let δ := min ds (da/Cs)
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < δ := lt_min hds (div_pos hda hCs)
  refine ⟨C,hC,δ,hδ,c,hc,?_⟩
  intro G μ T b ε B D hnear hB hμB V _ _ _ m Q H Z η BQ hH hZ hN hη hηc
  obtain ⟨S,hSμ,hST,hSgap,hSpivot,hword,hcoord,hgain,htotal,hmass,hK,hKlog⟩ :=
    hschedule G μ T b ε B D (hnear.trans (min_le_left _ _)) hB hμB
  subst μ
  subst T
  have hs0 : 0 ≤ ε+S.μ*S.T := add_nonneg D.tolerance_nonnegative
    (mul_nonneg D.mu_positive.le (zero_le_one.trans D.scale_lower))
  have hεa : Cs*(ε+S.μ*S.T) ≤ da := by
    have hd := (le_div_iff₀ hCs).mp (min_le_right ds (da/Cs))
    have hp := mul_le_mul_of_nonneg_left hnear hCs.le
    nlinarith only [hd,hp]
  have hk_eq : S.k = lastExcess S.μ S.T G.gaps (G.pivots b) := by
    simp only [PhaseSchedule.k,hSgap,hSpivot]
  obtain ⟨F,n,P,hPword,hPend,hPB,hPgate,hwithin,hold,hrel,hbound⟩ :=
    hattach S G (logarithmicStep S.μ) (Cs*(ε+S.μ*S.T)) (Cs*S.μ*S.T) (Cs*S.μ*S.T)
      (20*S.μ*b) (cappedStep S.μ B b-1-drawdown ((G.gaps 3).map (logarithmicStep S.μ)))
      (mul_nonneg hCs.le hs0) hεa hK (fun i _ => hcoord i) htotal hgain hmass hKlog V m Q H Z η BQ
      (by simpa only [hk_eq] using hH) (by simpa only [hk_eq] using hZ)
      (by simpa only [hSgap,hk_eq] using hN) hη hηc
  have hcost0 : Ca*Cs ≤ C := by
    dsimp [C]
    have hp : 0 ≤ (Ca+4)*Cs := by positivity
    linarith only [hp,hCa]
  have hcostT : (Ca+4)*Cs ≤ C := by
    dsimp [C]
    have hp : 0 ≤ Ca*Cs := mul_nonneg hCa.le hCs.le
    linarith only [hp,hCa]
  have hcostJ : Ca ≤ C := by
    dsimp [C]
    have hp : 0 ≤ Ca*Cs := mul_nonneg hCa.le hCs.le
    have hq : 0 ≤ (Ca+4)*Cs := by positivity
    linarith only [hp,hq]
  have hcostb : (40:ℝ) ≤ C := by
    dsimp [C]
    have hp : 0 ≤ Ca*Cs := mul_nonneg hCa.le hCs.le
    have hq : 0 ≤ (Ca+4)*Cs := by positivity
    linarith only [hp,hq,hCa]
  have hμT : 0 ≤ S.μ*S.T := mul_nonneg D.mu_positive.le (zero_le_one.trans D.scale_lower)
  have hμb : 0 ≤ S.μ*b := mul_nonneg D.mu_positive.le (by linarith only [D.exterior_lower])
  have hJ : 0 ≤ η+S.k*Z := add_nonneg hη (mul_nonneg S.k_positive.le BQ.offset_nonnegative)
  have hsum : 0 ≤ |rootGain (logarithmicStep S.μ) G.tree|+|rootGain (logarithmicStep S.μ) G.left|+
      |rootGain (logarithmicStep S.μ) G.right| := by positivity
  have hp0 := mul_le_mul_of_nonneg_right hcost0 (mul_nonneg hs0 hsum)
  have hpT := mul_le_mul_of_nonneg_right hcostT hμT
  have hpJ := mul_le_mul_of_nonneg_right hcostJ hJ
  have hpb := mul_le_mul_of_nonneg_right hcostb hμb
  have hfinal : signedThreeGain (rootGain (logarithmicStep S.μ) G.tree)
        (rootGain (logarithmicStep S.μ) G.left) (rootGain (logarithmicStep S.μ) G.right)-
        C*(ε+S.μ*S.T)*(|rootGain (logarithmicStep S.μ) G.tree|+|rootGain (logarithmicStep S.μ) G.left|+
          |rootGain (logarithmicStep S.μ) G.right|)-C*(S.μ*S.T+S.μ*b+η+S.k*Z) ≤
      Real.log ((‖Q.x 0‖^2/‖P.x 0‖^2)*
        (G.tree.prefixMass (logarithmicStep S.μ)/(cappedStep S.μ B b-1-drawdown ((G.gaps 3).map (logarithmicStep S.μ))))^2) := by
    nlinarith only [hbound,hp0,hpT,hpJ,hpb]
  refine ⟨S.LocalQueryIndex ⊕ Fin m,inferInstance,F,Sum.inr,n,P,?_,hPend,hPB,hPgate,hwithin,hold,?_,?_⟩
  · simpa only [hword] using hPword
  · exact hrel
  · simpa only [hk_eq] using hfinal

end
end StrongSilver.ScheduleTree.FourGapGroup
