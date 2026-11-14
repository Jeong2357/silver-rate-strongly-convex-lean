-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseQueryHeights
import StrongSilver.FourPhaseSourceBounds

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2800000

variable {x : Shape} (R : Regular x)
include R

theorem source_query_upper (hz : 0 ≤ x 7) (i : Fin 4) {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) :
    inner ℝ (source x) (c • (foot x i+s • slope x i)) ≤
    (totalTime x+q x)*inner ℝ (slope x i) (c • (foot x i+s • slope x i)) := by
  let z := c • (foot x i+s • slope x i)
  have h0 := query_dominates R hz i 0 hs hc
  have h1 := query_dominates R hz i 1 hs hc
  have h2 := query_dominates R hz i 2 hs hc
  have h3 := query_dominates R hz i 3 hs hc
  change inner ℝ (slope0 x) z ≤ inner ℝ (slope x i) z at h0
  change inner ℝ (slope1 x) z ≤ inner ℝ (slope x i) z at h1
  change inner ℝ (slope2 x) z ≤ inner ℝ (slope x i) z at h2
  change inner ℝ (slope3 x) z ≤ inner ℝ (slope x i) z at h3
  change inner ℝ (source x) z ≤ _
  rw [source_decomposition]
  simp only [inner_add_left,real_inner_smul_left]
  have hm0 := mul_le_mul_of_nonneg_left h0 R.t0_positive.le
  have hm1 := mul_le_mul_of_nonneg_left h1 R.t1_positive.le
  have hm2 := mul_le_mul_of_nonneg_left h2 R.t2_positive.le
  have hm3 := mul_le_mul_of_nonneg_left h3 R.q_positive.le
  unfold totalTime
  nlinarith only [hm0,hm1,hm2,hm3]

theorem first_query_height_renewal (hz : 0 ≤ x 7) (hTq : totalTime x+q x ≤ 6)
    (hm : ∀ i : Fin 3, (1/2:ℝ) ≤ x (i.castLE (by decide : 3 ≤ 8)))
    (hzsmall : x 7 ≤ 1/16) (i : Fin 3) {c s : ℝ} (hc : 1/2 ≤ c) (hs : 0 ≤ s) :
    inner ℝ (source x) (c • (foot x i.castSucc+s • slope x i.castSucc)) ≤
      8*planeValue x i.castSucc (c • (foot x i.castSucc+s • slope x i.castSucc)) := by
  have hc0 : 0 ≤ c := by linarith only [hc]
  have hupper := source_query_upper R hz i.castSucc hc0 hs
  have hh := first_queries_height_bound R hz hm i hc0 hs
  have ha := R.a_positive
  have hca := mul_le_mul_of_nonneg_right hc ha.le
  have hza := mul_le_mul_of_nonneg_left hzsmall ha.le
  have hdot : 0 ≤ inner ℝ (slope x i.castSucc) (c • (foot x i.castSucc+s • slope x i.castSucc)) := by
    nlinarith only [hh,hca,ha]
  have hcap := mul_le_mul_of_nonneg_right hTq hdot
  unfold planeValue
  nlinarith only [hupper,hh,hca,hza,hcap]

theorem last_query_source_zero {c s : ℝ} :
    inner ℝ (source x) (c • (foot x 3+s • slope x 3)) = 0 := by
  change inner ℝ (source x) (c • (foot3 x+s • slope3 x)) = 0
  rw [real_inner_smul_right,inner_add_right,real_inner_smul_right,source_foot3 R,source_slope3_inner R]
  ring

theorem query_height_renewal (hz : 0 ≤ x 7) (ha : a x ≤ 1/2) (hTq : totalTime x+q x ≤ 6)
    (hm : ∀ i : Fin 3, (1/2:ℝ) ≤ x (i.castLE (by decide : 3 ≤ 8)))
    (hzsmall : x 7 ≤ 1/16) (i : Fin 4) {c s : ℝ} (hc : 1/2 ≤ c) (hs : 0 ≤ s) :
    inner ℝ (source x) (c • (foot x i+s • slope x i)) ≤
      8*planeValue x i (c • (foot x i+s • slope x i)) := by
  fin_cases i
  · exact first_query_height_renewal R hz hTq hm hzsmall 0 hc hs
  · exact first_query_height_renewal R hz hTq hm hzsmall 1 hc hs
  · exact first_query_height_renewal R hz hTq hm hzsmall 2 hc hs
  · change inner ℝ (source x) (c • (foot x 3+s • slope x 3)) ≤
        8*planeValue x 3 (c • (foot x 3+s • slope x 3))
    rw [last_query_source_zero R]
    exact mul_nonneg (by norm_num) (last_queries_value_nonnegative R hz ha hc hs)

end
end StrongSilver.FourPhase
