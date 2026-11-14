-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedSplitInput

namespace StrongSilver.PaddedSplitInput
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

/-- The unbalanced vertex charge in (4.11), for the actual signed words
and the terminal reserve. The absolute constant is chosen once. -/
theorem unbalanced_excess_charge : ∃ c > 0, ∀ S : PaddedSplitInput, ∀ δ : ℝ,
    0 ≤ δ → δ ≤ 1 → ¬ S.Balanced δ → c*S.weight*δ^2 ≤ S.excess := by
  obtain ⟨c,hc,C,hC,hstable⟩ := split_stability
  refine ⟨c,hc,?_⟩
  intro S δ hδ hδ1 hnot
  let cost := (Real.log (S.a/(rho*S.t)))^2+(Real.log (S.b/(rho*S.t)))^2+(S.a+S.b+S.t-S.z)/S.t
  have hb := (hstable S.a S.b S.t S.z S.valid.1 S.valid.2.1 S.t_positive S.valid.2.2.2.1 S.valid.2.2.2.2.1).1
  change c*S.weight*min 1 cost ≤ S.excess at hb
  have hδsq : δ^2 ≤ 1 := by nlinarith only [hδ,hδ1]
  have hbad : δ < |Real.log (S.a/(rho*S.t))| ∨ δ < |Real.log (S.b/(rho*S.t))| ∨ δ < drawdown S.left/S.t := by
    simpa only [Balanced,not_and_or,not_le] using hnot
  have hcost : δ^2 ≤ cost := by
    rcases hbad with hbad | hbad | hbad
    · have hs := (sq_le_sq₀ hδ (abs_nonneg (Real.log (S.a/(rho*S.t))))).mpr hbad.le
      rw [sq_abs] at hs
      dsimp only [cost]
      nlinarith only [hs,sq_nonneg (Real.log (S.b/(rho*S.t))),S.deficit_nonnegative]
    · have hs := (sq_le_sq₀ hδ (abs_nonneg (Real.log (S.b/(rho*S.t))))).mpr hbad.le
      rw [sq_abs] at hs
      dsimp only [cost]
      nlinarith only [hs,sq_nonneg (Real.log (S.a/(rho*S.t))),S.deficit_nonnegative]
    · have hd := (le_div_iff₀ S.t_positive).mp hbad.le
      have ht : δ*S.t ≤ S.t := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ1 S.t_positive.le
      have hp : δ*S.t ≤ S.pivot+prefixMax S.right := ht.trans S.pivot_right_ge_time
      have hmin := le_min hd hp
      rw [← S.valid.2.2.2.2.2] at hmin
      have hdiv := (le_div_iff₀ S.t_positive).mpr hmin
      dsimp only [cost]
      nlinarith only [hdiv,hδ,hδ1,sq_nonneg (Real.log (S.a/(rho*S.t))),sq_nonneg (Real.log (S.b/(rho*S.t)))]
  exact (mul_le_mul_of_nonneg_left (le_min hδsq hcost) (mul_nonneg hc.le S.weight_positive.le)).trans hb

/-- At a balanced vertex the weighted left drawdown is paid directly
by its excess, with the same signed-word deficit identity. -/
theorem drawdown_excess_charge : ∃ c > 0, ∀ S : PaddedSplitInput,
    drawdown S.left/S.t ≤ 1 → c*S.weight*(drawdown S.left/S.t) ≤ S.excess := by
  obtain ⟨c,hc,C,hC,hstable⟩ := split_stability
  refine ⟨c,hc,?_⟩
  intro S hsmall
  have hd := (div_le_one S.t_positive).mp hsmall
  have hdx := hd.trans S.pivot_right_ge_time
  have hdef := S.valid.2.2.2.2.2
  rw [min_eq_left hdx] at hdef
  have hb := (hstable S.a S.b S.t S.z S.valid.1 S.valid.2.1 S.t_positive S.valid.2.2.2.1 S.valid.2.2.2.2.1).1
  change c*S.weight*min 1 ((Real.log (S.a/(rho*S.t)))^2+(Real.log (S.b/(rho*S.t)))^2+(S.a+S.b+S.t-S.z)/S.t) ≤ S.excess at hb
  rw [hdef] at hb
  have hcost : drawdown S.left/S.t ≤
      (Real.log (S.a/(rho*S.t)))^2+(Real.log (S.b/(rho*S.t)))^2+drawdown S.left/S.t := by
    linarith only [sq_nonneg (Real.log (S.a/(rho*S.t))),sq_nonneg (Real.log (S.b/(rho*S.t)))]
  exact (mul_le_mul_of_nonneg_left (le_min hsmall hcost) (mul_nonneg hc.le S.weight_positive.le)).trans hb

/-- Coarse weighted gain control, used when deleting bad vertices from
an actual binary forest. -/
theorem weighted_gain_charge : ∃ C > 0, ∀ S : PaddedSplitInput,
    S.weight*|S.gain| ≤ C*S.weight+C*S.excess := by
  obtain ⟨c,hc,C,hC,hstable⟩ := split_stability
  refine ⟨C,hC,?_⟩
  intro S
  have hb := (hstable S.a S.b S.t S.z S.valid.1 S.valid.2.1 S.t_positive S.valid.2.2.2.1 S.valid.2.2.2.2.1).2
  change |S.gain| ≤ C*(1+S.excess/S.weight) at hb
  have hp := mul_le_mul_of_nonneg_left hb S.weight_positive.le
  have he : S.weight*(C*(1+S.excess/S.weight)) = C*S.weight+C*S.excess := by
    field_simp [S.weight_positive.ne'] <;> ring
  simpa only [he] using hp

end
end StrongSilver.PaddedSplitInput
