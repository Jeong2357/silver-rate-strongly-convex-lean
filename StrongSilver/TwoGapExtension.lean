-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TwoGapTrace
import StrongSilver.TwoGapLogAccounting
import StrongSilver.CartesianDepthLogImprovement
import StrongSilver.PhaseTraceExtensions
import StrongSilver.CutMasses

namespace StrongSilver
open Real Filter Scalar.SignedIntervals
open ScheduleTree ScheduleTree.FourGapGroup
noncomputable section
set_option maxHeartbeats 4800000

/-- Finite lower bound for a disjoint pair's gain over the two ordinary
reference factors. The error uses the original tree and common budgets. -/
def twoGapScore (C μ B ε L U A : ℝ) (d : ℕ) (t : ScheduleTree) (bv : ℝ) : ℝ :=
  silverDepthGain (cappedStep μ B) d t-
    C*(ε+μ*t.prefixMass (logarithmicStep μ))*(levelSum (fun s => |rootGain (logarithmicStep μ) s|) d t+
      levelSum (fun s => |rootGain (logarithmicStep μ) s|) (d+1) t)-
    C*(2:ℝ)^d*(μ*t.prefixMass (logarithmicStep μ)+μ*U+workingGateFraction A+2*U*A^(-(1:ℝ)/20)/L)-
    8*t.gapDrawdown (cappedStep μ B)/(cappedStep μ B bv)

/-- The actual two-gap construction supplies the suffix-independent
extension used by the disjoint matching. All trajectory and interpolation
objects are constructed; the hypotheses are local numeric bounds. -/
theorem eventually_two_gap_extension : ∃ C > 0, ∃ τ > 0, ∃ c > 0, ∀ᶠ A : ℝ in atTop,
    ∀ μ B ε L U bv br T P : ℝ, ∀ d : ℕ, ∀ t : ScheduleTree, ∀ hr : List ℝ,
    0 < μ → 0 ≤ B → μ*B ≤ 1/10000 → μ*bv ≤ 1/10000 → 0 ≤ ε →
    ε+μ*t.prefixMass (logarithmicStep μ) ≤ τ →
    t.Cartesian → (∀ s ∈ t.word, s ≤ B) → 0 < bv → (∀ s ∈ t.word, s ≤ bv) →
    balancedThrough (logarithmicStep μ) ε (d+2) t →
    1000 ≤ L → L ≤ (1/4:ℝ)^(d+2)*t.prefixMass (logarithmicStep μ) → bv ≤ U →
    negativeMass t.word ≤ L/1000 → 2*U*negativeMass t.word ≤ c*L^2 →
    2*U*A^(-(1:ℝ)/20) ≤ c*L →
    OrdinaryPhaseParameters A μ br T P hr →
    ∀ i : Fin hr.length, A^((499:ℝ)/500) ≤ hr.get i → negativeMass hr ≤ hr.get i/16 →
    64*L ≤ hr.get i → μ*transformedGapMaximum μ hr ≤ 1/1000 →
    transformedGapMaximum μ hr+1 ≤ (14/5:ℝ)*cappedStep μ B bv →
    OrdinaryPhaseParameters A μ bv T P t.word → 1 ≤ P → 2*P ≤ bv →
    4*t.gapDrawdown (cappedStep μ B) ≤ cappedStep μ B bv →
    WordTraceExtension A μ ((t.word++[bv])++(hr++[br]))
      (((ordinaryReferenceFactor A μ bv P t.word)^2*(ordinaryReferenceFactor A μ br P hr)^2)*
        Real.exp (twoGapScore C μ B ε L U A d t bv)) := by
  obtain ⟨C,hC,τ,hτ,c,hc,htwo⟩ := eventually_two_gap_trace
  obtain ⟨τu,hτu,huniform⟩ := exists_uniform_groups_radius (by norm_num : (0:ℝ) < 1)
  refine ⟨C,hC,min τ (min τu (1/100)),lt_min hτ (lt_min hτu (by norm_num)),c,hc,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),htwo] with A hA htwo
  intro μ B ε L U bv br T P d t hr hμ hB hμB hμbv hε hnear hcart hword hbv hdom hbal hL hLdepth hbU hN hNbudget
    hZbudget Wr i hroot hNr hLroot hμmr hMr Wl hP hb hdraw s Mo Go r hr0 Q
  have hnearτ := hnear.trans (min_le_left _ _)
  have hnearτu := hnear.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε100 : ε ≤ 1/100 := by
    have hm := mul_nonneg hμ.le (prefixMass_positive (logarithmicStep μ) t).le
    have hh := hnear.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith only [hm,hh]
  obtain ⟨qs,Z,hZ,hZmax,hqs,⟨R⟩⟩ := htwo μ B ε L U bv br T P d t hr hμ hB hμB hμbv hε hnearτ hcart hword hbv hdom hbal
    hL hLdepth hbU hN hNbudget hZbudget Wr i hroot hNr hLroot hμmr hMr s Mo Go r Q
  have W := huniform c μ B ε L U d t bv qs hμ hB hμB hμbv hε hnearτu hcart hword hbv hdom hbal hqs
    hL hLdepth hbU hN hNbudget
  have hcap : μ*B ≤ 1/2 := by linarith only [hμB]
  have hLpos : 0 < L := by linarith only [hL]
  have hU : 0 ≤ U := hbv.le.trans hbU
  have hη : 0 ≤ workingGateFraction A := (Real.rpow_pos_of_pos (zero_lt_one.trans hA) _).le
  have hg := depth_log_improvement hC.le W hqs hbal hε100 hword hLpos hμ hcap hU hη hZ hZmax hP hb hdraw
  have hprefix := capped_gapPrefix_eq hμ (show μ*B < 1 by linarith only [hμB]) t.word hword
  change prefixMax (t.transformedWord (cappedStep μ B)) = transformedGapMaximum μ t.word at hprefix
  rw [hprefix] at hg
  have hpos := positiveExcessThrough_capped hword (balancedThrough_positive (hε100.trans_lt (by norm_num)) hbal)
  have hφ := cappedStep_ge hμ (show μ*B < 1 by linarith only [hμB]) bv
  have hφpos := hbv.trans_le hφ
  have hnum : 0 < cappedStep μ B bv-1-t.gapDrawdown (cappedStep μ B) := by
    nlinarith only [hdraw,hP,hb,hφ]
  have hterm : 0 < terminalFactor (cappedStep μ B) t bv := div_pos hnum (prefixMass_positive _ _)
  have hseq := (depth_sequence_log_rate (C := C) (ε := ε) (η := workingGateFraction A) (Z := Z) hqs hword hpos hterm).1
  have hrefL := Wl.reference_factor_positive hA
  have hrefR := Wr.reference_factor_positive hA
  have hm := transformedGapMaximum_nonnegative hμ t.word (Wl.small_steps (zero_lt_one.trans hA))
  have hcost : 0 ≤ 1200/Real.log A+μ*transformedGapMaximum μ t.word := by
    exact add_nonneg (div_nonneg (by norm_num) (Real.log_pos hA).le) (mul_nonneg hμ.le hm)
  have hlog : twoGapScore C μ B ε L U A d t bv ≤
      Real.log ((ordinaryReferenceFactor A μ br P hr)^2*sequenceRate C μ B ε (workingGateFraction A) qs Z)-
        2*Real.log (ordinaryReferenceFactor A μ bv P t.word)-2*Real.log (ordinaryReferenceFactor A μ br P hr) := by
    rw [Real.log_mul (sq_pos_of_pos hrefR).ne' hseq.ne',Real.log_pow,Wl.log_reference_factor hA]
    change twoGapScore C μ B ε L U A d t bv ≤ _
    change twoGapScore C μ B ε L U A d t bv ≤
      Real.log (sequenceRate C μ B ε (workingGateFraction A) qs Z)-
        2*Real.log ((bv-P)/(transformedGapMaximum μ t.word+P)) at hg
    linarith only [hg,hcost]
  have hfactor := factor_lower_of_normalized_log (mul_pos (sq_pos_of_pos hrefR) hseq) hrefL hrefR hlog
  have hrate := mul_le_mul_of_nonneg_left hfactor hr0
  have hrate' : r*(((ordinaryReferenceFactor A μ bv P t.word)^2*(ordinaryReferenceFactor A μ br P hr)^2)*
      Real.exp (twoGapScore C μ B ε L U A d t bv)) ≤
      (r*(ordinaryReferenceFactor A μ br P hr)^2)*sequenceRate C μ B ε (workingGateFraction A) qs Z := by
    nlinarith only [hrate]
  have result := R.weaken le_rfl le_rfl le_rfl hrate'
  simpa only [List.append_assoc] using Nonempty.intro result

end
end StrongSilver
