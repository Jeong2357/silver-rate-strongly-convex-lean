-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SplitLemma

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 1600000

/-- The terminal reserve passes to the right child. This statement allows
every positive pad, including the unit pad used in the band averages. -/
theorem padded_gap_split_masses (L R : List ℝ) {h P reserve : ℝ}
    (hP : 0 < P) (hr : 0 ≤ reserve) (hh : P < h) :
    let a := prefixMax L+P
    let b := prefixMax R+P+reserve
    let z := prefixMax (L++h::R)+P+reserve
    let t := h-P
    0 < a ∧ 0 < b ∧ 0 < t ∧ a ≤ z ∧ z ≤ a+b+t ∧
      a+b+t-z = min (drawdown L) (h+prefixMax R) := by
  dsimp only
  have hmL := prefixMax_nonneg L
  have hmR := prefixMax_nonneg R
  have hd := drawdown_nonneg L
  rw [max_plus_split]
  have he : prefixMax L+P+(prefixMax R+P+reserve)+(h-P)-
      (prefixMax L+max 0 (h+prefixMax R-drawdown L)+P+reserve) = min (drawdown L) (h+prefixMax R) := by
    by_cases hc : drawdown L ≤ h+prefixMax R
    · rw [max_eq_right (by linarith only [hc]),min_eq_left hc]
      ring
    · rw [max_eq_left (by linarith only [hc]),min_eq_right (le_of_not_ge hc)]
      ring
  have hmin : 0 ≤ min (drawdown L) (h+prefixMax R) := le_min hd (by linarith only [hmR,hP,hh])
  refine ⟨by linarith only [hmL,hP],by linarith only [hmR,hP,hr],sub_pos.mpr hh,?_,?_,he⟩
  · have hx := le_max_left 0 (h+prefixMax R-drawdown L)
    linarith only [hx,hr]
  · linarith only [he,hmin]

theorem padded_gap_power_decrease (L R : List ℝ) {h P reserve : ℝ}
    (hP : 0 < P) (hr : 0 ≤ reserve) (hh : P < h) :
    powerDecrease (prefixMax L+P) (prefixMax R+P+reserve) (prefixMax (L++h::R)+P+reserve) ≤
      splitCoefficient*(h-P)^nu*splitGain (prefixMax L+P) (prefixMax R+P+reserve) (h-P) (prefixMax (L++h::R)+P+reserve) := by
  obtain ⟨ha,hb,ht,haz,hz,_⟩ := padded_gap_split_masses L R hP hr hh
  exact split_power_decrease_le _ _ _ _ ha hb ht haz hz

theorem padded_gap_excess : ∃ c > 0, ∀ L R : List ℝ, ∀ h P reserve : ℝ,
    0 < P → 0 ≤ reserve → P < h →
    c*(h-P)^nu*min 1 (drawdown L/(h-P)) ≤
      splitExcess (prefixMax L+P) (prefixMax R+P+reserve) (h-P) (prefixMax (L++h::R)+P+reserve) := by
  obtain ⟨c,hc,C,hC,hbound⟩ := split_stability
  refine ⟨c,hc,?_⟩
  intro L R h P reserve hP hr hh
  obtain ⟨ha,hb,ht,haz,hz,hdef⟩ := padded_gap_split_masses L R hP hr hh
  have he := (hbound _ _ _ _ ha hb ht haz hz).1
  have hlog : 0 ≤ (Real.log ((prefixMax L+P)/(rho*(h-P))))^2+
      (Real.log ((prefixMax R+P+reserve)/(rho*(h-P))))^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcost : min 1 ((prefixMax L+P+(prefixMax R+P+reserve)+(h-P)-
      (prefixMax (L++h::R)+P+reserve))/(h-P)) ≤
      min 1 ((Real.log ((prefixMax L+P)/(rho*(h-P))))^2+
        (Real.log ((prefixMax R+P+reserve)/(rho*(h-P))))^2+
        (prefixMax L+P+(prefixMax R+P+reserve)+(h-P)-(prefixMax (L++h::R)+P+reserve))/(h-P)) :=
    min_le_min_left 1 (by linarith only [hlog])
  rw [hdef,Scalar.Bands.capped_deficit (drawdown L) (h+prefixMax R) (h-P) ht
    (by have hx := prefixMax_nonneg R; linarith only [hx,hP])] at hcost
  rw [hdef] at he
  exact (mul_le_mul_of_nonneg_left hcost (mul_nonneg hc.le (Real.rpow_pos_of_pos ht nu).le)).trans he

end
end StrongSilver
