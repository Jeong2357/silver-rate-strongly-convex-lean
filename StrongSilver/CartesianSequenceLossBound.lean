-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianGroupLogRate
import StrongSilver.CartesianUniformGroups

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

def absoluteThreeGain (μ : ℝ) (G : FourGapGroup) : ℝ :=
  |rootGain (logarithmicStep μ) G.tree|+|rootGain (logarithmicStep μ) G.left|+|rootGain (logarithmicStep μ) G.right|

theorem firstOffset_nonnegative {qs : List Group} {Z : ℝ} (hZ : 0 ≤ Z) : 0 ≤ firstOffset qs Z := by
  cases qs
  · exact hZ
  · exact le_rfl

theorem firstOffset_le {qs : List Group} {Z Zmax : ℝ} (hZmax : 0 ≤ Zmax) (hZ : Z ≤ Zmax) :
    firstOffset qs Z ≤ Zmax := by cases qs <;> assumption

theorem UniformGroups.last_excess_upper {δ c μ B ε L U : ℝ} {qs : List Group}
    (W : UniformGroups δ c μ B ε L U qs) (hL : 0 < L) (hμB : μ*B ≤ 1/2)
    {q : Group} (hq : q ∈ qs) :
    0 < lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2) ∧
    lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2) ≤ 2*U/L := by
  have D := W.data q hq
  have hφ := cappedStep_ge D.mu_positive (show μ*B < 1 by linarith only [hμB]) q.2
  have hφpos : 0 < cappedStep μ B q.2 := by linarith only [hφ,D.exterior_lower]
  have hTkpos : 0 < groupScale μ q*lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2) := by
    nlinarith only [W.time_lower q hq,hφpos]
  have hk : 0 < lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2) :=
    (mul_pos_iff.mp hTkpos).elim (fun h => h.2)
      (fun h => False.elim ((not_lt_of_ge (zero_le_one.trans D.scale_lower)) h.1))
  have hmul := mul_le_mul_of_nonneg_right (W.scale_lower q hq) hk.le
  refine ⟨hk,(le_div_iff₀ hL).mpr ?_⟩
  nlinarith only [hmul,W.time_upper q hq,W.boundary_upper q hq]

/-- All finite losses over the constructed original groups are bounded
by the endpoint gain sum plus a common error times the group count.
The count is at most 2^d for an actual depth partition. -/
theorem sequenceLoss_uniform_bound {δ c μ B ε L U M Zmax η Z : ℝ} {qs : List Group}
    (W : UniformGroups δ c μ B ε L U qs) (hL : 0 < L) (hμ : 0 ≤ μ) (hμB : μ*B ≤ 1/2)
    (hT : ∀ q ∈ qs, groupScale μ q ≤ M) (hZ : 0 ≤ Z) (hZmax : Z ≤ Zmax) :
    sequenceLoss μ ε η qs Z ≤ (ε+μ*M)*(qs.map fun q => absoluteThreeGain μ q.1).sum+
      (qs.length:ℝ)*(μ*M+μ*U+η+2*U*Zmax/L) := by
  have hZmax0 : 0 ≤ Zmax := hZ.trans hZmax
  induction qs with
  | nil => simp [sequenceLoss]
  | cons q qs ih =>
    have hq : q ∈ q::qs := by simp
    have Wtail := W.restrict (List.sublist_cons_self q qs)
    have hTtail : ∀ p ∈ qs, groupScale μ p ≤ M := fun p hp => hT p (List.mem_cons_of_mem q hp)
    have htail := ih Wtail hTtail
    have hk := W.last_excess_upper hL hμB hq
    have hz0 := firstOffset_nonnegative (qs := qs) hZ
    have hzmax := firstOffset_le (qs := qs) hZmax0 hZmax
    have hU0 : 0 ≤ U := by
      have D := W.data q hq
      linarith only [D.exterior_lower,W.boundary_upper q hq]
    have hoffset : lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2)*firstOffset qs Z ≤ 2*U*Zmax/L := by
      have hp := mul_le_mul hk.2 hzmax hz0 (div_nonneg (by positivity) hL.le)
      have he : (2*U/L)*Zmax = 2*U*Zmax/L := by ring
      simpa only [he] using hp
    have htime := mul_le_mul_of_nonneg_left (hT q hq) hμ
    have hboundary := mul_le_mul_of_nonneg_left (W.boundary_upper q hq) hμ
    have habs : 0 ≤ absoluteThreeGain μ q.1 := by dsimp [absoluteThreeGain]; positivity
    have hg := mul_le_mul_of_nonneg_right (show ε+μ*groupScale μ q ≤ ε+μ*M by linarith only [htime]) habs
    have hlocal : groupLoss q.1 μ (groupScale μ q) q.2 ε η (firstOffset qs Z) ≤
      (ε+μ*M)*absoluteThreeGain μ q.1+(μ*M+μ*U+η+2*U*Zmax/L) := by
      change (ε+μ*groupScale μ q)*absoluteThreeGain μ q.1+μ*groupScale μ q+μ*q.2+η+
        lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2)*firstOffset qs Z ≤ _
      linarith only [hg,htime,hboundary,hoffset]
    simp only [sequenceLoss,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hlocal,htail]

end
end StrongSilver.ScheduleTree.FourGapGroup
