-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianBalancedAttachment
import StrongSilver.FourPhaseTrace
import StrongSilver.AttachmentRatios

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

def leadingFactor (G : FourGapGroup) (μ B b : ℝ) : ℝ :=
  (cappedStep μ B b-1-drawdown ((G.gaps 3).map (logarithmicStep μ)))/G.tree.prefixMass (logarithmicStep μ)

def gainLower (C : ℝ) (G : FourGapGroup) (μ T b ε η Z : ℝ) : ℝ :=
  signedThreeGain (rootGain (logarithmicStep μ) G.tree)
    (rootGain (logarithmicStep μ) G.left) (rootGain (logarithmicStep μ) G.right)-
    C*(ε+μ*T)*(|rootGain (logarithmicStep μ) G.tree|+|rootGain (logarithmicStep μ) G.left|+
      |rootGain (logarithmicStep μ) G.right|)-
    C*(μ*T+μ*b+η+lastExcess μ T G.gaps (G.pivots b)*Z)

theorem BalancedGroupData.exterior_excess_positive {G : FourGapGroup} {μ T b ε B : ℝ}
    (D : BalancedGroupData G μ T b ε) (hμB : μ*B ≤ 1/2) :
    0 < cappedStep μ B b-1-drawdown ((G.gaps 3).map (logarithmicStep μ)) := by
  have hcap : μ*B < 1 := by linarith only [hμB]
  have hφ := cappedStep_ge D.mu_positive hcap b
  linarith only [hφ,D.exterior_lower,D.exterior_drawdown]

theorem source_ratio_lower_of_log {r M K L : ℝ} (hr : 0 < r) (hM : 0 < M) (hK : 0 < K)
    (h : L ≤ Real.log (r*(M/K)^2)) : Real.exp L*(K/M)^2 ≤ r := by
  have he := Real.exp_le_exp.mpr h
  rw [Real.exp_log (mul_pos hr (sq_pos_of_pos (div_pos hM hK)))] at he
  have hp := mul_le_mul_of_nonneg_right he (sq_nonneg (K/M))
  have hi : (M/K)^2*(K/M)^2 = 1 := by field_simp <;> ring
  calc
    _ ≤ (r*(M/K)^2)*(K/M)^2 := hp
    _ = r := by rw [mul_assoc,hi,mul_one]

/-- One step of the actual backward assembly in a finite Euclidean
space. The returned trace has the exact original word, renewed scale T,
zero offset, and uniform directional bounds. -/
theorem exists_balanced_group_trace : ∃ C > 0, ∃ δ > 0, ∃ c > 0,
    ∀ G : FourGapGroup, ∀ μ T b ε B : ℝ,
    BalancedGroupData G μ T b ε → ε+μ*T ≤ δ → 0 ≤ B → μ*B ≤ 1/2 →
    ∀ H Z η ηo Mo Go r : ℝ, ∀ h : List ℝ, ∀ W : FourPhaseTrace μ h H Z ηo Mo Go r,
    H ≤ T*lastExcess μ T G.gaps (G.pivots b)/2 → lastExcess μ T G.gaps (G.pivots b)*Z ≤ c →
    (∀ i : Fin 3, negativeMass (G.gaps i.castSucc) ≤ c*H/lastExcess μ T G.gaps (G.pivots b)) →
    0 ≤ η → η ≤ c →
    Nonempty (FourPhaseTrace μ ((G.tree.word++[b])++h) T 0 η 26 (1/T)
      (r*Real.exp (gainLower C G μ T b ε η Z)*(G.leadingFactor μ B b)^2)) := by
  obtain ⟨C,hC,δ,hδ,c,hc,hattach⟩ := balanced_group_attachment
  refine ⟨C,hC,δ,hδ,c,hc,?_⟩
  intro G μ T b ε B D hnear hB hμB H Z η ηo Mo Go r h W hH hZ hN hη hηc
  obtain ⟨ι,_,F,keep,n,P,hword,hend,hPB,hgate,hwithin,hold,hrel,hlog⟩ :=
    hattach G μ T b ε B D hnear hB hμB (Space W.dimension) W.length W.path H Z η W.suffix_bounds
      hH hZ hN hη hηc
  have hK := D.exterior_excess_positive hμB
  have hM := prefixMass_positive (logarithmicStep μ) G.tree
  have hrsource : 0 < ‖W.path.x 0‖^2/‖P.x 0‖^2 := div_pos
    (sq_pos_of_pos (norm_pos_iff.mpr W.nonzero)) (sq_pos_of_pos (norm_pos_iff.mpr hPB.source_nonzero))
  have hsource := source_ratio_lower_of_log hrsource hM hK hlog
  change Real.exp (gainLower C G μ T b ε η Z)*(G.leadingFactor μ B b)^2 ≤
    ‖W.path.x 0‖^2/‖P.x 0‖^2 at hsource
  have hlastnorm : ‖P.x (Fin.last n)‖ = ‖W.path.x (Fin.last W.length)‖ := by
    rw [hend]
    exact retainedIsometry.norm_map _
  have hactual : ‖P.x (Fin.last n)‖^2/‖P.x 0‖^2 =
      (‖W.path.x (Fin.last W.length)‖^2/‖W.path.x 0‖^2)*(‖W.path.x 0‖^2/‖P.x 0‖^2) := by
    rw [hlastnorm]
    field_simp [norm_ne_zero_iff.mpr W.nonzero,norm_ne_zero_iff.mpr hPB.source_nonzero] <;> ring
  have hfactor : 0 ≤ Real.exp (gainLower C G μ T b ε η Z)*(G.leadingFactor μ B b)^2 :=
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hratio : r*Real.exp (gainLower C G μ T b ε η Z)*(G.leadingFactor μ B b)^2 ≤
      ‖P.x (Fin.last n)‖^2/‖P.x 0‖^2 := by
    rw [hactual]
    have hp := mul_le_mul W.ratio hsource hfactor (div_nonneg (sq_nonneg _) (sq_nonneg _))
    simpa only [mul_assoc] using hp
  exact ⟨FourPhaseTrace.ofPath P (by simpa only [W.steps_eq] using hword) hPB hgate hrel hratio⟩

end
end StrongSilver.ScheduleTree.FourGapGroup
