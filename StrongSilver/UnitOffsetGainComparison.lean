-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AdjustedTimePower
import StrongSilver.LogMassPerturbation

namespace StrongSilver.PaddedSplitInput
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 4200000

/-- Offset-one gain on the same actual signed words. Its adjusted
selected factor removes the left drawdown. -/
def unitOffsetGain (S : PaddedSplitInput) : ℝ :=
  splitGain (prefixMax S.left+1) (prefixMax S.right+1)
    (S.pivot-1-drawdown S.left) (prefixMax (S.left++S.pivot::S.right)+1)

private theorem splitGain_expanded {a b t z : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hz : 0 < z) :
    splitGain a b t z = Real.log t+Real.log z-Real.log a-Real.log b := by
  rw [splitGain,Real.log_div (mul_pos ht hz).ne' (mul_pos ha hb).ne',
    Real.log_mul ht.ne' hz.ne',Real.log_mul ha.ne' hb.ne']
  ring

/-- Changing only the pad from P to one has error at most 8P/t on an
actual balanced nonterminal split. -/
theorem unit_offset_gain_comparison {S : PaddedSplitInput} {δ : ℝ}
    (hP : 1 ≤ S.pad) (hsmall : S.pad ≤ S.t/4) (hres : S.reserve = 0)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4) (h : S.Balanced δ) :
    |S.unitOffsetGain-S.adjustedGain| ≤ 8*S.pad/S.t := by
  let a₁ := prefixMax S.left+1
  let b₁ := prefixMax S.right+1
  let z₁ := prefixMax (S.left++S.pivot::S.right)+1
  let k₁ := S.pivot-1-drawdown S.left
  have ht := S.t_positive
  have hs : 0 < S.t/2 := by positivity
  have hm := balanced_mass_bounds hδ hδmax h
  have hd := balanced_drawdown_identity hδmax h
  have ha : a₁-S.a = 1-S.pad := by dsimp only [a₁,a]; ring
  have hb : b₁-S.b = 1-S.pad := by dsimp only [b₁,b]; rw [hres]; ring
  have hz : z₁-S.z = 1-S.pad := by dsimp only [z₁,z]; rw [hres]; ring
  have hk : k₁-S.adjustedTime = S.pad-1 := by dsimp only [k₁,adjustedTime,t]; ring
  have hT : S.t/2 ≤ S.adjustedTime := by dsimp only [adjustedTime]; linarith only [hd.2,ht]
  have ha₁ : S.t/2 ≤ a₁ := by linarith only [ha,hm.1,hsmall,ht]
  have hb₁ : S.t/2 ≤ b₁ := by linarith only [hb,hm.2.2.1,hsmall,ht]
  have hz₁ : S.t/2 ≤ z₁ := by linarith only [hz,hm.2.2.2.2.1,hsmall,ht]
  have hk₁ : S.t/2 ≤ k₁ := by linarith only [hk,hT,hP]
  have htA : S.t/2 ≤ S.a := by linarith only [hm.1,ht]
  have htB : S.t/2 ≤ S.b := by linarith only [hm.2.2.1,ht]
  have htZ : S.t/2 ≤ S.z := by linarith only [hm.2.2.2.2.1,ht]
  have hpad := S.pad_positive.le
  have haDiff : |a₁-S.a| ≤ S.pad := by rw [ha]; exact abs_le.mpr ⟨by linarith only [hP],by linarith only [hP]⟩
  have hbDiff : |b₁-S.b| ≤ S.pad := by rw [hb]; exact abs_le.mpr ⟨by linarith only [hP],by linarith only [hP]⟩
  have hzDiff : |z₁-S.z| ≤ S.pad := by rw [hz]; exact abs_le.mpr ⟨by linarith only [hP],by linarith only [hP]⟩
  have hkDiff : |k₁-S.adjustedTime| ≤ S.pad := by rw [hk]; exact abs_le.mpr ⟨by linarith only [hP],by linarith only [hP]⟩
  have hLA := abs_le.mp (log_mass_perturbation hs ha₁ htA hpad haDiff)
  have hLB := abs_le.mp (log_mass_perturbation hs hb₁ htB hpad hbDiff)
  have hLZ := abs_le.mp (log_mass_perturbation hs hz₁ htZ hpad hzDiff)
  have hLK := abs_le.mp (log_mass_perturbation hs hk₁ hT hpad hkDiff)
  change |splitGain a₁ b₁ k₁ z₁-splitGain S.a S.b S.adjustedTime S.z| ≤ _
  rw [splitGain_expanded (hs.trans_le ha₁) (hs.trans_le hb₁) (hs.trans_le hk₁) (hs.trans_le hz₁),
    splitGain_expanded S.valid.1 S.valid.2.1 (hs.trans_le hT) (hs.trans_le htZ)]
  have hdiv : S.pad/(S.t/2) = 2*S.pad/S.t := by field_simp
  rw [hdiv] at hLA hLB hLZ hLK
  exact abs_le.mpr ⟨by linear_combination hLK.1+hLZ.1+hLA.2+hLB.2,by linear_combination hLK.2+hLZ.2+hLA.1+hLB.1⟩

end
end StrongSilver.PaddedSplitInput
