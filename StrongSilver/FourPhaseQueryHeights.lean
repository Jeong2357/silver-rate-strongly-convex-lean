-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseComparisons

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 3400000

theorem slope3_axis (x : Shape) : slope3 x = (-1:ℝ) • axis := by
  rw [slope3,axis,point_smul]
  congr 1 <;> ring

theorem foot0_axis {x : Shape} (R : Regular x) : inner ℝ (foot0 x) axis = -x 0*a x := by
  rw [foot0,inner_sub_left,real_inner_smul_left,source_orthogonal_axis R]
  change 0-x 0*inner ℝ (point _ _ _ _) axis = _
  rw [point_inner_axis]
  ring

variable {x : Shape} (R : Regular x)
include R

theorem first_feet_axis_bound {m : ℝ} (hm : ∀ i : Fin 3, m ≤ x (i.castLE (by decide : 3 ≤ 8))) (i : Fin 3) :
    a x*m ≤ -inner ℝ (foot x i.castSucc) axis := by
  have ha := R.a_positive
  have hq := a_mul_totalTime x R.totalTime_positive.ne'
  fin_cases i
  · change a x*m ≤ -inner ℝ (foot0 x) axis
    rw [foot0_axis R]
    have hh := hm 0
    change m ≤ x 0 at hh
    nlinarith only [mul_le_mul_of_nonneg_left hh ha.le]
  · change a x*m ≤ -inner ℝ (foot1 x) axis
    rw [foot1_formula R,point_inner_axis,foot1_axis_negative R]
    have hML : m ≤ leftMass x := by
      have hh := hm 1; change m ≤ x 1 at hh
      unfold leftMass; linarith only [hh,R.m0_positive,R.k0_positive]
    nlinarith only [mul_le_mul_of_nonneg_left hML ha.le]
  · change a x*m ≤ -inner ℝ (foot2 x) axis
    rw [foot2_formula R,point_inner_axis]
    have hm2 := hm 2
    change m ≤ x 2 at hm2
    have hT : m ≤ totalTime x-x 6 := by
      unfold totalTime t2
      linarith only [hm2,R.t0_positive,R.t1_positive]
    have hh := mul_le_mul_of_nonneg_left hT ha.le
    nlinarith only [hh,hq]

theorem first_feet_height_bound {m : ℝ} (hz : 0 ≤ x 7)
    (hm : ∀ i : Fin 3, m ≤ x (i.castLE (by decide : 3 ≤ 8))) (i : Fin 3) :
    a x*m ≤ inner ℝ (slope x i.castSucc) (foot x i.castSucc) := by
  have hd := foot_dominates R hz i.castSucc 3
  change 0 ≤ inner ℝ (foot x i.castSucc) (slope x i.castSucc-slope3 x) at hd
  rw [inner_sub_right,slope3_axis,real_inner_smul_right] at hd
  have hb := first_feet_axis_bound R hm i
  rw [real_inner_comm (foot x i.castSucc)]
  linarith only [hd,hb]

theorem first_queries_height_bound {m c s : ℝ} (hz : 0 ≤ x 7)
    (hm : ∀ i : Fin 3, m ≤ x (i.castLE (by decide : 3 ≤ 8))) (i : Fin 3) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    c*a x*m ≤ inner ℝ (slope x i.castSucc) (c • (foot x i.castSucc+s • slope x i.castSucc)) := by
  have hh := first_feet_height_bound R hz hm i
  have hnorm : 0 ≤ inner ℝ (slope x i.castSucc) (slope x i.castSucc) := real_inner_self_nonneg
  have hprice := mul_nonneg hs hnorm
  have hmul := mul_le_mul_of_nonneg_left hh hc
  rw [real_inner_smul_right,inner_add_right,real_inner_smul_right]
  nlinarith only [hmul,mul_nonneg hc hprice]

def planeValue (x : Shape) (i : Fin 4) (z : Coordinates) : ℝ := inner ℝ (slope x i) z-a x*x 7

theorem first_queries_value_positive {c s : ℝ} (hz : 0 ≤ x 7)
    (hm : ∀ i : Fin 3, (1/2:ℝ) ≤ x (i.castLE (by decide : 3 ≤ 8))) (i : Fin 3)
    (hc : 1/2 ≤ c) (hs : 0 ≤ s) (hzsmall : x 7 ≤ 1/16) :
    0 < planeValue x i.castSucc (c • (foot x i.castSucc+s • slope x i.castSucc)) := by
  have hh := first_queries_height_bound R hz hm i (by linarith only [hc]) hs
  have ha := R.a_positive
  have hca := mul_le_mul_of_nonneg_right hc ha.le
  have hza := mul_le_mul_of_nonneg_left hzsmall ha.le
  unfold planeValue
  nlinarith only [hh,hca,hza,ha]

theorem last_queries_value_nonnegative {c s : ℝ} (hz : 0 ≤ x 7)
    (ha : a x ≤ 1/2) (hc : 1/2 ≤ c) (hs : 0 ≤ s) :
    0 ≤ planeValue x 3 (c • (foot x 3+s • slope x 3)) := by
  change 0 ≤ inner ℝ (slope3 x) (c • (foot3 x+s • slope3 x))-a x*x 7
  rw [foot3_formula,slope3,point_smul,point_add,point_smul,point_inner]
  have h1 := mul_le_mul_of_nonneg_right hc hz
  have h2 := mul_le_mul_of_nonneg_right ha hz
  have h3 := mul_nonneg (show 0 ≤ c by linarith only [hc]) hs
  nlinarith only [h1,h2,h3]

end
end StrongSilver.FourPhase
