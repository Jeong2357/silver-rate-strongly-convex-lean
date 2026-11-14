-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseSourceBounds
import StrongSilver.FourPhaseOrbitQueries

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2400000

variable {x : Shape} (R : Regular x)
include R

theorem first_mass_upper (i : Fin 3) : phaseMass x i.castSucc ≤ totalTime x := by
  have h0 : x 0 ≤ t0 x := by unfold t0; linarith only [R.k0_positive]
  have h1 : x 1 ≤ t1 x := by unfold t1; linarith only [R.k1_positive]
  have h2 : x 2 ≤ t2 x := by unfold t2; linarith only [R.k2_positive]
  fin_cases i
  · change x 0 ≤ totalTime x
    unfold totalTime; linarith only [h0,R.t1_positive,R.t2_positive]
  · change x 1 ≤ totalTime x
    unfold totalTime; linarith only [h1,R.t0_positive,R.t2_positive]
  · change x 2 ≤ totalTime x
    unfold totalTime; linarith only [h2,R.t0_positive,R.t1_positive]

theorem source_feet_upper (ht0 : 1 ≤ t0 x) (ht1 : 1 ≤ t1 x) (hT : totalTime x ≤ 6) (i : Fin 4) :
    inner ℝ (source x) (foot x i) ≤ 6*‖source x‖^2 := by
  have hnorm := sq_nonneg ‖source x‖
  have hg1 := source_slopes_upper R ht0 ht1 1
  have hg0 := (source_slope0_positive R).le
  have hkT : x 5 ≤ totalTime x := by
    unfold totalTime t1
    linarith only [R.t0_positive,R.m1_positive,R.t2_positive]
  have hk6 : x 5 ≤ 6 := hkT.trans hT
  fin_cases i
  · change inner ℝ (source x) (foot0 x) ≤ _
    rw [foot0,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    nlinarith only [mul_nonneg R.m0_positive.le hg0,hnorm]
  · change inner ℝ (source x) (foot1 x) ≤ _
    rw [source_foot1 R]
    change inner ℝ (source x) (slope1 x) ≤ _ at hg1
    have h1 := mul_le_mul_of_nonneg_left hg1 R.k1_positive.le
    have h2 := mul_le_mul_of_nonneg_right hk6 hnorm
    exact h1.trans h2
  · change inner ℝ (source x) (foot2 x) ≤ _
    rw [source_foot2 R]; nlinarith only [hnorm]
  · change inner ℝ (source x) (foot3 x) ≤ _
    rw [source_foot3 R]; nlinarith only [hnorm]

theorem source_query_relative_upper (ht0 : 1 ≤ t0 x) (ht1 : 1 ≤ t1 x) (hT : totalTime x ≤ 6)
    (i : Fin 4) {c s : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 2) (hs : 0 ≤ s) (hs7 : s ≤ 7) :
    inner ℝ (source x) (c • (foot x i+s • slope x i)) ≤ 26*‖source x‖^2 := by
  have hfoot := source_feet_upper R ht0 ht1 hT i
  have hslope := source_slopes_upper R ht0 ht1 i
  have hfoot0 := source_feet_nonnegative R i
  have hslope0 := source_slopes_nonnegative R i
  have hn := sq_nonneg ‖source x‖
  have h1 := mul_le_mul_of_nonneg_left hslope hs
  have h2 := mul_le_mul_of_nonneg_right hs7 hn
  have h3 := mul_le_mul_of_nonneg_left (add_le_add hfoot (h1.trans h2)) hc
  have h4 := mul_le_mul_of_nonneg_right hc2
    (show 0 ≤ 6*‖source x‖^2+7*‖source x‖^2 by nlinarith only [hn])
  rw [real_inner_smul_right,inner_add_right,real_inner_smul_right]
  nlinarith only [h3,h4]

end
end StrongSilver.FourPhase
