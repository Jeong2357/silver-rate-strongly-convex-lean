-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SilverOffsetBalance
import StrongSilver.CartesianProductTimeShape
import StrongSilver.FourPhaseGainPairBound

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase
noncomputable section
set_option maxHeartbeats 3000000

/-- Actual product-time parameters and their three logarithmic gains
on a balanced original four-gap block. All constants are absolute; the
error in the gains is proportional to mu*T, rather than to the balance
tolerance. This distinction is needed when summing over depth groups. -/
theorem exists_balanced_product_constants : ∃ C > 0, ∃ δ > 0,
    ∀ G : FourGapGroup, ∀ μ K T b ε : ℝ,
    T = G.first.prefixMass (logarithmicStep μ) →
    0 < μ → μ ≤ 1 → 1 ≤ K → 1 ≤ T → 0 ≤ ε →
    μ*absoluteMass (boundedWord G.gaps (G.pivots b)) ≤ 1/4 → μ*(K*T) ≤ 1 →
    (∀ i, transformedGapMaximum μ (G.gaps i)+1 ≤ K*T) →
    (∀ i, |phaseDuration μ G.gaps (G.pivots b) i| ≤ K*T) →
    absoluteMass (boundedWord G.gaps (G.pivots b)) ≤ K*T →
    SilverBalanced (logarithmicStep μ) ε G.left →
    SilverBalanced (logarithmicStep μ) ε G.right →
    SilverBalanced (logarithmicStep μ) ε G.tree →
    ε+(12*K^2+2*K)*μ*T ≤ δ →
    (∀ i, |productShape μ T G.gaps (G.pivots b) 0 i-reference i| ≤
      C*(ε+(12*K^2+2*K)*μ*T)) ∧
    (|gain (productShape μ T G.gaps (G.pivots b) 0)-rootGain (logarithmicStep μ) G.tree|+
      |gainLeft (productShape μ T G.gaps (G.pivots b) 0)-rootGain (logarithmicStep μ) G.left|+
      |gainRight (productShape μ T G.gaps (G.pivots b) 0)-rootGain (logarithmicStep μ) G.right| ≤
        C*(12*K^2+2*K)*μ*T) := by
  obtain ⟨Cm,hCm,dm,hdm,hm⟩ := exists_balanced_shape_constants
  obtain ⟨Cg,hCg,dg,hdg,hg⟩ := exists_gain_pair_box
  let C := Cm+Cg+1
  let δ := min dm (min (1/2) (dg/(Cm+1)))
  have hCp : 0 < Cm+1 := by linarith only [hCm]
  have hδ : 0 < δ := lt_min hdm (lt_min (by norm_num) (div_pos hdg hCp))
  refine ⟨C,by dsimp [C]; linarith only [hCm,hCg],δ,hδ,?_⟩
  intro G μ K T b ε hTeq hμ hμ1 hK hT hε hsmall hscale hmass htime habsolute hL hR hM hnear
  let e := (12*K^2+2*K)*μ*T
  change ε+e ≤ δ at hnear
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact mul_nonneg (mul_nonneg (by nlinarith only [sq_nonneg K,hK0]) hμ.le) (zero_le_one.trans hT)
  have hεd : ε ≤ δ := by change ε+e ≤ δ at hnear; linarith only [hnear,he0]
  have hεδm := hεd.trans (min_le_left dm _)
  have hε1 : ε < 1 := hεd.trans_lt ((min_le_right dm _).trans_lt
    ((min_le_left (1/2:ℝ) _).trans_lt (by norm_num)))
  have hKL := positive_excess_of_balance hL hε1
  have hKR := positive_excess_of_balance hR hε1
  have hKM := positive_excess_of_balance hM hε1
  have hgeom := hm G (logarithmicStep μ) ε hε hεδm hL hR hM
  have hdiff := G.productShape_massShape_error hμ hμ1 hK hT hsmall hscale hKL hmass htime habsolute
  have hCm1 : 1 ≤ Cm+1 := by linarith only [hCm]
  have hbudget : Cm*ε+e ≤ dg := by
    have hδg : δ ≤ dg/(Cm+1) := (min_le_right _ _).trans (min_le_right _ _)
    have hprod := (le_div_iff₀ hCp).mp hδg
    have hh := mul_le_mul_of_nonneg_left hnear hCp.le
    have hce := mul_nonneg hCm.le he0
    nlinarith only [hprod,hh,hce,hε]
  have hmassBox : ∀ i, |G.massShape (logarithmicStep μ) (G.first.prefixMass (logarithmicStep μ)) i-reference i| ≤ dg := by
    intro i
    exact (hgeom i).trans (by linarith only [hbudget,he0])
  have hCcm : Cm ≤ C := by dsimp [C]; linarith only [hCg]
  have hC1 : 1 ≤ C := by dsimp [C]; linarith only [hCm,hCg]
  have hCgC : Cg ≤ C := by dsimp [C]; linarith only [hCm]
  have hproduct (hTeq : T = G.first.prefixMass (logarithmicStep μ)) (i : Fin 8) :
      |productShape μ T G.gaps (G.pivots b) 0 i-reference i| ≤ Cm*ε+e := by
    have ht := abs_add_le
      (productShape μ T G.gaps (G.pivots b) 0 i-G.massShape (logarithmicStep μ) T i)
      (G.massShape (logarithmicStep μ) T i-reference i)
    rw [sub_add_sub_cancel] at ht
    have hb := hgeom i
    rw [← hTeq] at hb
    have hd := hdiff i
    change |productShape μ T G.gaps (G.pivots b) 0 i-G.massShape (logarithmicStep μ) T i| ≤ e at hd
    linarith only [ht,hd,hb]
  constructor
  · intro i
    have hx := hproduct hTeq i
    have h1 := mul_le_mul_of_nonneg_right hCcm hε
    have h2 := mul_le_mul_of_nonneg_right hC1 he0
    dsimp only [e] at hx h2
    nlinarith only [hx,h1,h2]
  · have hpair := hg (productShape μ T G.gaps (G.pivots b) 0)
      (G.massShape (logarithmicStep μ) T)
      (fun i => (hproduct hTeq i).trans hbudget)
      (by simpa only [hTeq] using hmassBox) e he0 hdiff
    have hgain := G.gains_massShape (logarithmicStep μ) T (ne_of_gt (zero_lt_one.trans_le hT)) hKL hKR hKM
    rw [hgain.1,hgain.2.1,hgain.2.2] at hpair
    have hb := hpair.trans (mul_le_mul_of_nonneg_right hCgC he0)
    simpa only [e,mul_assoc] using hb

end
end StrongSilver.ScheduleTree.FourGapGroup
