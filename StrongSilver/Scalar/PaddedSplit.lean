-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusLemma
import StrongSilver.Scalar.SignedIntervals

namespace StrongSilver.Scalar.Bands
open Set StrongSilver.Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 1000000

theorem padded_split_masses (L R : List ℝ) (h B Λ : ℝ) (hB : 2 ≤ B) (hΛ : 0 ≤ Λ) (hh : B < h) :
    let a := prefixMax L+B
    let b := prefixMax R+B+Λ
    let z := prefixMax (L++h::R)+B+Λ
    let t := h-B
    0 < a ∧ 0 < b ∧ 0 < t ∧ a ≤ z ∧ z ≤ a+b+t ∧
      a+b+t-z=min (drawdown L) (h+prefixMax R) := by
  dsimp only
  have hmL := prefixMax_nonneg L
  have hmR := prefixMax_nonneg R
  have hd := drawdown_nonneg L
  rw [max_plus_split]
  have hid : prefixMax L+B+(prefixMax R+B+Λ)+(h-B)-
      (prefixMax L+max 0 (h+prefixMax R-drawdown L)+B+Λ)=min (drawdown L) (h+prefixMax R) := by
    by_cases hc : drawdown L ≤ h+prefixMax R
    · rw [max_eq_right (by linarith),min_eq_left hc]
      ring
    · rw [max_eq_left (by linarith),min_eq_right (le_of_not_ge hc)]
      ring
  have hmin : 0 ≤ min (drawdown L) (h+prefixMax R) := le_min hd (by linarith)
  refine ⟨by linarith,by linarith,by linarith,?_,?_,hid⟩
  · have hx := le_max_left 0 (h+prefixMax R-drawdown L)
    linarith
  · linarith

/-- Truncating the deficit at the pivot scale eliminates the capped debt. -/
theorem capped_deficit (d x t : ℝ) (ht : 0 < t) (hxt : t ≤ x) :
    min 1 ((min d x)/t)=min 1 (d/t) := by
  rw [← div_self ht.ne',min_div_div_right ht.le,min_div_div_right ht.le]
  congr 1
  calc
    min t (min d x)=min d (min t x) := by rw [← min_assoc,min_comm t d,min_assoc]
    _ = min t d := by rw [min_eq_left hxt,min_comm]

/-- The full padded split lemma: the original signed parent/child masses,
exact capped-debt identity, and excess lower bound with an absolute constant. -/
theorem padded_split : ∃ c > 0, ∀ L R : List ℝ, ∀ h B Λ : ℝ,
    2 ≤ B → 0 ≤ Λ → B < h →
    let a := prefixMax L+B
    let b := prefixMax R+B+Λ
    let z := prefixMax (L++h::R)+B+Λ
    let t := h-B
    a ≤ z ∧ z ≤ a+b+t ∧ a+b+t-z=min (drawdown L) (h+prefixMax R) ∧
      c*t^Silver.nu*min 1 (drawdown L/t) ≤ Silver.excess a b t z := by
  obtain ⟨c,hc,C,hC,hbound⟩ := Silver.max_plus_excess
  refine ⟨c,hc,fun L R h B Λ hB hΛ hh => ?_⟩
  dsimp only
  obtain ⟨ha,hb,ht,haz,hz,hdef⟩ := padded_split_masses L R h B Λ hB hΛ hh
  refine ⟨haz,hz,hdef,?_⟩
  have he := (hbound _ _ _ _ ha hb ht haz hz).1
  have hlog : 0 ≤ (Real.log ((prefixMax L+B)/(Silver.rho*(h-B))))^2+
      (Real.log ((prefixMax R+B+Λ)/(Silver.rho*(h-B))))^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcost : min 1 ((prefixMax L+B+(prefixMax R+B+Λ)+(h-B)-
      (prefixMax (L++h::R)+B+Λ))/(h-B)) ≤
      min 1 ((Real.log ((prefixMax L+B)/(Silver.rho*(h-B))))^2+
        (Real.log ((prefixMax R+B+Λ)/(Silver.rho*(h-B))))^2+
        (prefixMax L+B+(prefixMax R+B+Λ)+(h-B)-(prefixMax (L++h::R)+B+Λ))/(h-B)) :=
    min_le_min_left 1 (by linarith)
  rw [hdef,capped_deficit (drawdown L) (h+prefixMax R) (h-B) ht (by have := prefixMax_nonneg R; linarith)] at hcost
  rw [hdef] at he
  exact (mul_le_mul_of_nonneg_left hcost (mul_nonneg hc.le (Real.rpow_pos_of_pos ht Silver.nu).le)).trans he

end
end StrongSilver.Scalar.Bands
