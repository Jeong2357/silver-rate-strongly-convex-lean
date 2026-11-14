-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianDepthRateIdentity
import StrongSilver.CartesianDepthLossBound
import StrongSilver.CartesianExteriorLogComparison

namespace StrongSilver.ScheduleTree.FourGapGroup
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

/-- Finite logarithmic improvement of the actual left-gap depth
construction over its ordinary reference factor. The signed S_d and the
two endpoint gain levels are those of the original capped Cartesian tree. -/
theorem depth_log_improvement {δ c C μ B ε L U Zmax η Z P : ℝ}
    {d : ℕ} {t : ScheduleTree} {b : ℝ} {qs : List Group}
    (hC : 0 ≤ C) (W : UniformGroups δ c μ B ε L U qs)
    (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b)
    (hbal : balancedThrough (logarithmicStep μ) ε (d+2) t) (hε : ε ≤ 1/100)
    (hword : ∀ s ∈ t.word, s ≤ B) (hL : 0 < L) (hμ : 0 < μ)
    (hμB : μ*B ≤ 1/2) (hU : 0 ≤ U) (hη : 0 ≤ η) (hZ : 0 ≤ Z) (hZmax : Z ≤ Zmax)
    (hP : 1 ≤ P) (hb : 2*P ≤ b)
    (hdraw : 4*t.gapDrawdown (cappedStep μ B) ≤ cappedStep μ B b) :
    silverDepthGain (cappedStep μ B) d t-
      C*(ε+μ*t.prefixMass (logarithmicStep μ))*(levelSum (fun s => |rootGain (logarithmicStep μ) s|) d t+
        levelSum (fun s => |rootGain (logarithmicStep μ) s|) (d+1) t)-
      C*(2:ℝ)^d*(μ*t.prefixMass (logarithmicStep μ)+μ*U+η+2*U*Zmax/L)-
      8*t.gapDrawdown (cappedStep μ B)/(cappedStep μ B b) ≤
    Real.log (sequenceRate C μ B ε η qs Z)-
      2*Real.log ((b-P)/(prefixMax (t.transformedWord (cappedStep μ B))+P)) := by
  have hpos := positiveExcessThrough_capped hword
    (balancedThrough_positive (hε.trans_lt (by norm_num)) hbal)
  have hcap : μ*B < 1 := by linarith only [hμB]
  have hφ := cappedStep_ge hμ hcap b
  have hm := prefixMax_nonneg (t.transformedWord (cappedStep μ B))
  have hd := gapDrawdown_nonnegative (cappedStep μ B) t
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hbpos : 0 < b := by linarith only [hPpos,hb]
  have hφpos : 0 < cappedStep μ B b := hbpos.trans_le hφ
  have hnum : 0 < cappedStep μ B b-1-t.gapDrawdown (cappedStep μ B) := by
    nlinarith only [hdraw,hP,hb,hφ]
  have hterm : 0 < terminalFactor (cappedStep μ B) t b := div_pos hnum (prefixMass_positive _ _)
  have hidentity := depth_sequence_log_rate (C := C) (ε := ε) (η := η) (Z := Z) hqs hword hpos hterm
  have hloss := depth_sequence_loss_bound W hqs hbal hε hL hμ.le hμB hU hη hZ hZmax
  have hprice := mul_le_mul_of_nonneg_left hloss hC
  have hext := exterior_factor_log_comparison hm hP hb hφ hd hdraw
  change -4*t.gapDrawdown (cappedStep μ B)/(cappedStep μ B b) ≤
    Real.log ((terminalFactor (cappedStep μ B) t b)/
      ((b-P)/(prefixMax (t.transformedWord (cappedStep μ B))+P))) at hext
  have hold : 0 < (b-P)/(prefixMax (t.transformedWord (cappedStep μ B))+P) :=
    div_pos (by linarith only [hb,hPpos]) (by linarith only [hm,hPpos])
  rw [Real.log_div hterm.ne' hold.ne'] at hext
  have hext2 := mul_le_mul_of_nonneg_left hext (by norm_num : (0:ℝ) ≤ 2)
  have he : 2*(-4*t.gapDrawdown (cappedStep μ B)/(cappedStep μ B b)) =
      -8*t.gapDrawdown (cappedStep μ B)/(cappedStep μ B b) := by ring
  rw [he] at hext2
  have hneg : -8*t.gapDrawdown (cappedStep μ B)/(cappedStep μ B b) =
      -(8*t.gapDrawdown (cappedStep μ B)/(cappedStep μ B b)) := by ring
  rw [hneg] at hext2
  nlinarith only [hidentity.2,hprice,hext2]

end
end StrongSilver.ScheduleTree.FourGapGroup
