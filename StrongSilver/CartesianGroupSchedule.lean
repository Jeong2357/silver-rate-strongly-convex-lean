-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianBalancedProductGains
import StrongSilver.CartesianWordBudgets
import StrongSilver.FourPhaseLastRelativeError
import StrongSilver.FourPhaseFiniteLemma

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

/-- Construct the full finite four-phase schedule record from balanced
original Cartesian groups. Absolute mass, phase durations, small products,
all seven near-reference coordinates, and gain comparison are derived. -/
theorem exists_balanced_group_schedule : ∃ C > 0, ∃ δ > 0,
    ∀ G : FourGapGroup, ∀ μ T b ε : ℝ,
    T = G.first.prefixMass (logarithmicStep μ) →
    0 < μ → 1 ≤ T → 0 ≤ ε → ε+μ*T ≤ δ →
    (∀ i, ∀ s ∈ G.gaps i, μ*s < 1) →
    (∀ i : Fin 3, 0 < G.pivots b i.castSucc ∧ μ*G.pivots b i.castSucc < 1) →
    SilverBalanced (logarithmicStep μ) ε G.left →
    SilverBalanced (logarithmicStep μ) ε G.right →
    SilverBalanced (logarithmicStep μ) ε G.tree →
    (∀ i, negativeMass (G.gaps i) ≤ T) →
    8 ≤ b → (4/5:ℝ)*T ≤ b →
    drawdown ((G.gaps 3).map (logarithmicStep μ)) ≤ b/8 → μ*b ≤ 1/100 →
    ∃ S : PhaseSchedule, S.μ = μ ∧ S.T = T ∧ S.gap = G.gaps ∧ S.pivot = G.pivots b ∧
      S.totalWord = G.tree.word++[b] ∧
      (∀ i, |S.shape 0 i-reference i| ≤ C*(ε+μ*T)) ∧
      |gain (S.shape 0)-rootGain (logarithmicStep μ) G.tree|+
      |gainLeft (S.shape 0)-rootGain (logarithmicStep μ) G.left|+
      |gainRight (S.shape 0)-rootGain (logarithmicStep μ) G.right| ≤ C*μ*T := by
  obtain ⟨Cb,hCb,db,hdb,hshape⟩ := exists_balanced_shape_constants
  obtain ⟨Cg,hCg,dg,hdg,hgains⟩ := exists_balanced_product_constants
  let E : ℝ := 120200
  let C := Cg*E
  let δ := min db (min (1/2) (min (1/(2*Cb)) (min (1/400) (dg/E))))
  have hE : 0 < E := by norm_num [E]
  have hE1 : 1 ≤ E := by norm_num [E]
  have hδ : 0 < δ := lt_min hdb (lt_min (by norm_num) (lt_min (by positivity) (lt_min (by norm_num) (div_pos hdg hE))))
  refine ⟨C,mul_pos hCg hE,δ,hδ,?_⟩
  intro G μ T b ε hTeq hμ hT hε hnear hsteps hpivot hL hR hM hnegative hb hbT hdb hμb
  have hTpos := zero_lt_one.trans_le hT
  have hμT : 0 ≤ μ*T := mul_nonneg hμ.le hTpos.le
  have hεd : ε ≤ δ := by linarith only [hnear,hμT]
  have hμTd : μ*T ≤ δ := by linarith only [hnear,hε]
  have hδdb : δ ≤ db := min_le_left _ _
  have hδhalf : δ ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδCb : δ ≤ 1/(2*Cb) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ400 : δ ≤ 1/400 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδdg : δ ≤ dg/E := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hε1 : ε < 1 := (hεd.trans hδhalf).trans_lt (by norm_num)
  have hKL := positive_excess_of_balance hL hε1
  have hmassShape := hshape G (logarithmicStep μ) ε hε (hεd.trans hδdb) hL hR hM
  have hCbε : Cb*ε ≤ 1/2 := by
    have hbound := (le_div_iff₀ (mul_pos (by norm_num) hCb)).mp (hεd.trans hδCb)
    nlinarith only [hbound]
  have hbudget := G.massShape_word_budgets hμ hT hsteps hpivot hKL
    (by simpa only [hTeq] using fun i => (hmassShape i).trans hCbε) hnegative (hμTd.trans hδ400)
  have hμle : μ ≤ 1/4 := by
    have hp := mul_le_mul_of_nonneg_left hT hμ.le
    nlinarith only [hp,hμTd.trans hδ400]
  have hd0 := drawdown_nonneg ((G.gaps 3).map (logarithmicStep μ))
  have hds : μ*drawdown ((G.gaps 3).map (logarithmicStep μ)) ≤ 1 := by
    have hp := mul_le_mul_of_nonneg_left hdb hμ.le
    nlinarith only [hp,hμb]
  have hlasterror := actual_last_excess_error hμ hTpos G.gaps (G.pivots b) hbudget.2.2.1
    (by change 0 ≤ b; linarith only [hb]) hds
  change |T*lastExcess μ T G.gaps (G.pivots b)-(b-1-drawdown ((G.gaps 3).map (logarithmicStep μ)))| ≤
    μ*(drawdown ((G.gaps 3).map (logarithmicStep μ)))^2+2*μ*b*drawdown ((G.gaps 3).map (logarithmicStep μ)) at hlasterror
  have hk := last_excess_lower_of_budget hμ hTpos hb hbT hd0 hdb hμb hlasterror
  let S : PhaseSchedule := {
    μ := μ, T := T, gap := G.gaps, pivot := G.pivots b,
    mu_positive := hμ, time_positive := hTpos, mu_upper := hμle,
    mu_time_upper := by linarith only [hμTd.trans hδ400],
    small_total := hbudget.2.2.1, last_excess_lower := hk }
  have hεg : ε+(12*(100:ℝ)^2+2*100)*μ*T ≤ dg := by
    have hp := (le_div_iff₀ hE).mp hδdg
    have hq := mul_le_mul_of_nonneg_left hnear hE.le
    have heε := mul_le_mul_of_nonneg_right hE1 hε
    dsimp only [E] at hp hq heε
    nlinarith only [hp,hq,heε]
  have hgain := hgains G μ 100 T b ε hTeq hμ (by linarith only [hμle]) (by norm_num) hT hε
    hbudget.2.2.1 hbudget.2.2.2.1 hbudget.1 hbudget.2.2.2.2 hbudget.2.1 hL hR hM hεg
  refine ⟨S,rfl,rfl,rfl,rfl,G.original_word b |>.symm,?_,?_⟩
  · intro i
    have hh := hgain.1 i
    change |productShape μ T G.gaps (G.pivots b) 0 i-reference i| ≤ C*(ε+μ*T)
    have heε := mul_le_mul_of_nonneg_right hE1 hε
    have hmul := mul_le_mul_of_nonneg_left heε hCg.le
    dsimp only [E,C] at heε hmul ⊢
    norm_num at hh
    nlinarith only [hh,hmul]
  · change |gain (productShape μ T G.gaps (G.pivots b) 0)-rootGain (logarithmicStep μ) G.tree|+
      |gainLeft (productShape μ T G.gaps (G.pivots b) 0)-rootGain (logarithmicStep μ) G.left|+
      |gainRight (productShape μ T G.gaps (G.pivots b) 0)-rootGain (logarithmicStep μ) G.right| ≤ C*μ*T
    dsimp only [C,E]
    norm_num at hgain
    exact hgain.2

end
end StrongSilver.ScheduleTree.FourGapGroup
