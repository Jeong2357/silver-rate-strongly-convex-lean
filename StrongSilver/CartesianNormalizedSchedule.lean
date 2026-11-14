-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianGroupSchedule
import StrongSilver.FourPhaseMassLogPairBound

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 4000000

/-- Numerical data on an actual original Cartesian four-gap group.
The scale, every word, every pivot and every transformed mass are fixed;
no interpolation or trajectory existence is included among the fields. -/
structure BalancedGroupData (G : FourGapGroup) (μ T b ε : ℝ) : Prop where
  scale_eq : T = G.first.prefixMass (logarithmicStep μ)
  mu_positive : 0 < μ
  scale_lower : 1 ≤ T
  tolerance_nonnegative : 0 ≤ ε
  gap_steps : ∀ i, ∀ s ∈ G.gaps i, μ*s < 1
  pivot_steps : ∀ i : Fin 3, 0 < G.pivots b i.castSucc ∧ μ*G.pivots b i.castSucc < 1
  left_balance : SilverBalanced (logarithmicStep μ) ε G.left
  right_balance : SilverBalanced (logarithmicStep μ) ε G.right
  root_balance : SilverBalanced (logarithmicStep μ) ε G.tree
  negative_mass : ∀ i, negativeMass (G.gaps i) ≤ T
  exterior_lower : 8 ≤ b
  exterior_scale : (4/5:ℝ)*T ≤ b
  exterior_drawdown : drawdown ((G.gaps 3).map (logarithmicStep μ)) ≤ b/8
  exterior_small : μ*b ≤ 1/100

/-- In addition to the exact original schedule and its Cartesian gains,
construct the positive normalization and both logarithmic comparison
errors needed by the actual tree-gain attachment. The exterior selected
step may lie above the capped-transform threshold B. -/
theorem exists_normalized_group_schedule : ∃ C > 0, ∃ δ > 0,
    ∀ G : FourGapGroup, ∀ μ T b ε B : ℝ,
    BalancedGroupData G μ T b ε → ε+μ*T ≤ δ → 0 ≤ B → μ*B ≤ 1/2 →
    ∃ S : PhaseSchedule, S.μ = μ ∧ S.T = T ∧ S.gap = G.gaps ∧ S.pivot = G.pivots b ∧
      S.totalWord = G.tree.word++[b] ∧
      (∀ i, |S.shape 0 i-reference i| ≤ C*(ε+μ*T)) ∧
      |gain (S.shape 0)-rootGain (logarithmicStep μ) G.tree|+
      |gainLeft (S.shape 0)-rootGain (logarithmicStep μ) G.left|+
      |gainRight (S.shape 0)-rootGain (logarithmicStep μ) G.right| ≤ C*μ*T ∧
      0 < totalMass (S.shape 0) ∧
      |Real.log (totalMass (S.shape 0))-Real.log (G.tree.prefixMass (logarithmicStep μ)/T)| ≤ C*μ*T ∧
      0 < cappedStep μ B b-1-drawdown ((G.gaps 3).map (logarithmicStep μ)) ∧
      |Real.log (T*S.k/(cappedStep μ B b-1-drawdown ((G.gaps 3).map (logarithmicStep μ))))| ≤ 20*μ*b := by
  obtain ⟨Cs,hCs,ds,hds,hschedule⟩ := exists_balanced_group_schedule
  obtain ⟨Cb,hCb,db,hdb,hshape⟩ := exists_balanced_shape_constants
  obtain ⟨Cm,hCm,dm,hdm,hmasslog⟩ := exists_mass_log_pair_box
  obtain ⟨dr,hdr,hregular⟩ := exists_regular_box
  let C := Cs+Cm*120200+1
  let δ := min ds (min db (min (1/2) (min (1/(2*Cb))
    (min (1/400) (min (dm/(Cs+Cb)) (dr/Cs))))))
  have hδ : 0 < δ := lt_min hds (lt_min hdb (lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by norm_num) (lt_min (by positivity) (div_pos hdr hCs))))))
  refine ⟨C,by dsimp [C]; positivity,δ,hδ,?_⟩
  intro G μ T b ε B D hnear hB hμB
  have hTpos := zero_lt_one.trans_le D.scale_lower
  have hμT : 0 ≤ μ*T := mul_nonneg D.mu_positive.le hTpos.le
  have hεd : ε ≤ δ := by linarith only [hnear,hμT]
  have hμTd : μ*T ≤ δ := by linarith only [hnear,D.tolerance_nonnegative]
  have hδds : δ ≤ ds := min_le_left _ _
  have hδdb : δ ≤ db := (min_le_right _ _).trans (min_le_left _ _)
  have hδhalf : δ ≤ 1/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδCb : δ ≤ 1/(2*Cb) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ400 : δ ≤ 1/400 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδdm : δ ≤ dm/(Cs+Cb) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδdr : δ ≤ dr/Cs := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  obtain ⟨S,hSμ,hST,hSgap,hSpivot,hword,hcoord,hgain⟩ := hschedule G μ T b ε D.scale_eq
    D.mu_positive D.scale_lower D.tolerance_nonnegative (hnear.trans hδds) D.gap_steps D.pivot_steps
    D.left_balance D.right_balance D.root_balance D.negative_mass D.exterior_lower D.exterior_scale
    D.exterior_drawdown D.exterior_small
  have hCbε : Cb*ε ≤ 1/2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hCb)).mp (hεd.trans hδCb)
    nlinarith only [hh]
  have hgeom := hshape G (logarithmicStep μ) ε D.tolerance_nonnegative (hεd.trans hδdb)
    D.left_balance D.right_balance D.root_balance
  have hbudget := G.massShape_word_budgets D.mu_positive D.scale_lower D.gap_steps D.pivot_steps
    (positive_excess_of_balance D.left_balance ((hεd.trans hδhalf).trans_lt (by norm_num)))
    (by simpa only [D.scale_eq] using fun i => (hgeom i).trans hCbε)
    D.negative_mass (hμTd.trans hδ400)
  have hdiff := G.productShape_massShape_error D.mu_positive
    (by have hh := mul_le_mul_of_nonneg_left D.scale_lower D.mu_positive.le; nlinarith only [hh,hμTd.trans hδ400])
    (by norm_num : (1:ℝ) ≤ 100) D.scale_lower hbudget.2.2.1 hbudget.2.2.2.1
    (positive_excess_of_balance D.left_balance ((hεd.trans hδhalf).trans_lt (by norm_num)))
    hbudget.1 hbudget.2.2.2.2 hbudget.2.1
  have hprodBox : ∀ i, |S.shape 0 i-reference i| ≤ dm := by
    intro i
    have hh := (le_div_iff₀ (add_pos hCs hCb)).mp hδdm
    have hp := mul_le_mul_of_nonneg_left hnear hCs.le
    have hc := mul_nonneg hCb.le hδ.le
    exact (hcoord i).trans (by nlinarith only [hh,hp,hc])
  have hmassBox : ∀ i, |G.massShape (logarithmicStep μ) T i-reference i| ≤ dm := by
    intro i
    have hh := (le_div_iff₀ (add_pos hCs hCb)).mp hδdm
    have hp := mul_le_mul_of_nonneg_left hεd hCb.le
    have hc := mul_nonneg hCs.le hδ.le
    have hx := hgeom i
    rw [← D.scale_eq] at hx
    exact hx.trans (by nlinarith only [hh,hp,hc])
  have hreg : Regular (S.shape 0) := hregular _ (fun i => (hcoord i).trans (by
    have hh := (le_div_iff₀ hCs).mp hδdr
    have hp := mul_le_mul_of_nonneg_left hnear hCs.le
    nlinarith only [hh,hp]))
  have hlog := hmasslog (S.shape 0) (G.massShape (logarithmicStep μ) T) hprodBox hmassBox
    ((12*(100:ℝ)^2+2*100)*μ*T)
    (mul_nonneg (mul_nonneg (by norm_num) D.mu_positive.le) hTpos.le) (by
      simpa only [PhaseSchedule.shape,hSμ,hST,hSgap,hSpivot] using hdiff)
  have hε1 : ε < 1 := (hεd.trans hδhalf).trans_lt (by norm_num)
  have hKL := positive_excess_of_balance D.left_balance hε1
  have hKR := positive_excess_of_balance D.right_balance hε1
  have hKM := positive_excess_of_balance D.root_balance hε1
  rw [G.totalMass_massShape (logarithmicStep μ) T hTpos.ne' hKL hKR hKM] at hlog
  have hd0 := drawdown_nonneg ((G.gaps 3).map (logarithmicStep μ))
  have hds : μ*drawdown ((G.gaps 3).map (logarithmicStep μ)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left D.exterior_drawdown D.mu_positive.le
    nlinarith only [hh,D.exterior_small]
  have he := actual_last_excess_error D.mu_positive hTpos G.gaps (G.pivots b) hbudget.2.2.1
    (by change 0 ≤ b; linarith only [D.exterior_lower]) hds
  change |T*lastExcess μ T G.gaps (G.pivots b)-(b-1-drawdown ((G.gaps 3).map (logarithmicStep μ)))| ≤
    μ*(drawdown ((G.gaps 3).map (logarithmicStep μ)))^2+2*μ*b*drawdown ((G.gaps 3).map (logarithmicStep μ)) at he
  obtain ⟨hφ,hφe⟩ := capped_step_error_le_square D.mu_positive hB
    (by linarith only [D.exterior_lower]) hμB
  obtain ⟨hK,_,hKlog⟩ := last_excess_log_error D.mu_positive hTpos
    (by linarith only [D.exterior_lower]) hd0
    (by linarith only [D.exterior_drawdown,D.exterior_lower]) hφ hφe he D.exterior_small
  have hCsC : Cs ≤ C := by
    dsimp [C]
    have hh : 0 ≤ Cm*120200 := by positivity
    linarith only [hh]
  have hCmC : Cm*120200 ≤ C := by dsimp [C]; linarith only [hCs]
  refine ⟨S,hSμ,hST,hSgap,hSpivot,hword,fun i => (hcoord i).trans
    (mul_le_mul_of_nonneg_right hCsC (add_nonneg D.tolerance_nonnegative hμT)),
    hgain.trans ?_,hreg.totalMass_positive,?_,hK,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hCsC hμT
    nlinarith only [hh]
  · have hh := mul_le_mul_of_nonneg_right hCmC hμT
    norm_num at hlog
    nlinarith only [hh,hlog]
  · simpa only [PhaseSchedule.k,hSμ,hST,hSgap,hSpivot] using hKlog

end
end StrongSilver.ScheduleTree.FourGapGroup
