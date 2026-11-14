-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseQueryHeights
import StrongSilver.SupportFamilies

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2600000

variable {x : Shape} (R : Regular x)
include R

theorem queries_value_nonnegative (hz : 0 ≤ x 7) (ha : a x ≤ 1/2)
    (hm : ∀ i : Fin 3, (1/2:ℝ) ≤ x (i.castLE (by decide : 3 ≤ 8)))
    (hzsmall : x 7 ≤ 1/16) (i : Fin 4) {c s : ℝ} (hc : 1/2 ≤ c) (hs : 0 ≤ s) :
    0 ≤ planeValue x i (c • (foot x i+s • slope x i)) := by
  fin_cases i
  · exact (first_queries_value_positive R hz hm 0 hc hs hzsmall).le
  · exact (first_queries_value_positive R hz hm 1 hc hs hzsmall).le
  · exact (first_queries_value_positive R hz hm 2 hc hs hzsmall).le
  · exact last_queries_value_nonnegative R hz ha hc hs

/-- Supporting data of the four affine planes, for any finite collection
of backward queries. The mutual interpolation inequalities are proved from
the explicit geometric construction. -/
def queryFamily {ι : Type*} (hz : 0 ≤ x 7) (ha : a x ≤ 1/2)
    (hm : ∀ i : Fin 3, (1/2:ℝ) ≤ x (i.castLE (by decide : 3 ≤ 8)))
    (hzsmall : x 7 ≤ 1/16) {T : ℝ} (hT : 0 < T)
    (phase : ι → Fin 4) (c s : ι → ℝ) (hc : ∀ j, 1/2 ≤ c j) (hs : ∀ j, 0 ≤ s j) :
    SupportFamily ι Coordinates where
  z := fun j => c j • (foot x (phase j)+s j • slope x (phase j))
  g := fun j => (1/T) • slope x (phase j)
  d := fun j => planeValue x (phase j) (c j • (foot x (phase j)+s j • slope x (phase j)))/T
  nonnegative := fun j => div_nonneg (queries_value_nonnegative R hz ha hm hzsmall (phase j) (hc j) (hs j)) hT.le
  origin := by
    intro j
    rw [real_inner_smul_left]
    have hh : 0 ≤ a x*x 7 := mul_nonneg R.a_positive.le hz
    unfold planeValue
    have hp := mul_nonneg hh (one_div_pos.mpr hT).le
    simp only [div_eq_mul_inv,one_div] at hp ⊢
    nlinarith only [hp]
  supports := by
    intro i j
    rw [real_inner_smul_left,inner_sub_right]
    unfold planeValue
    have hh := query_dominates R hz (phase j) (phase i) (hs j) (show 0 ≤ c j by linarith only [hc j])
    have hp := mul_le_mul_of_nonneg_left hh (one_div_pos.mpr hT).le
    simp only [div_eq_mul_inv,one_div] at hp ⊢
    nlinarith only [hp]

end
end StrongSilver.FourPhase
