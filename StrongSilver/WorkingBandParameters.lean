-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrdinaryPhaseParameters

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2000000

/-- The ordinary numerical conditions in Lemma 3.7 imply the closed phase
construction hypotheses. The threshold depends only on the fixed band
exponents, not on the schedule or curvature. -/
theorem eventually_working_band_parameters {σ τ υ : ℝ} (hσ : 0 < σ) (hσmax : σ ≤ 1/200)
    (hτ : 0 < τ) (hτmax : τ ≤ 1/1000) (hσυ : σ < υ) (hτυ : τ < υ) (hυmax : υ ≤ 1/50) :
    ∀ᶠ A : ℝ in atTop, ∀ μ b P : ℝ, ∀ h : List ℝ,
      0 < μ → μ*A^(1+υ) ≤ 31/32 → A^((499 : ℝ)/500) ≤ b → b ≤ A^(1+σ) →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      Scalar.SignedIntervals.positiveMass h ≤ A^(1+τ) →
      negativeLogSum h (A^(1+υ)) ≤ (1/250)*Real.log A →
      (∀ c ∈ h, 0 < c → c ≤ A) → OrdinaryPhaseParameters A μ b (A^(1+υ)) P h := by
  have hυ : 0 < υ := hσ.trans hσυ
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_const_mul_power_le (by linarith only [hυ] : -υ < 0) 2] with A hA hsmall
  simp only [Real.rpow_zero] at hsmall
  intro μ b P h hμ hμT hbLower hbUpper hPLower hPUpper hmass hE hcap
  have hA0 : 0 < A := zero_lt_one.trans hA
  let T := A^(1+υ)
  have hT : 0 < T := Real.rpow_pos_of_pos hA0 _
  have hbT : b < T := hbUpper.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hA (by linarith only [hσυ]))
  have hquot : A/T = A^(-υ) := by
    calc
      _ = A^(1 : ℝ)/A^(1+υ) := by rw [Real.rpow_one]
      _ = A^((1 : ℝ)-(1+υ)) := (Real.rpow_sub hA0 _ _).symm
      _ = _ := by congr 1; ring
  have hAT : A/T ≤ 1/2 := by rw [hquot]; linarith only [hsmall]
  have hTimePow : A^(1+τ)/T = A^(τ-υ) := by
    dsimp only [T]
    rw [← Real.rpow_sub hA0]
    congr 1
    ring
  have hmassTime := div_le_div_of_nonneg_right hmass hT.le
  rw [hTimePow] at hmassTime
  have htime1 : A^(τ-υ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA.le (by linarith only [hτυ])
  have hmassPivot : Scalar.SignedIntervals.positiveMass h/b ≤ A^((3 : ℝ)/1000) := by
    have hbp : 0 < b := (Real.rpow_pos_of_pos hA0 _).trans_le hbLower
    calc
      _ ≤ A^(1+τ)/b := div_le_div_of_nonneg_right hmass hbp.le
      _ ≤ A^(1+τ)/A^((499 : ℝ)/500) := div_le_div_of_nonneg_left
        (Real.rpow_pos_of_pos hA0 _).le (Real.rpow_pos_of_pos hA0 _) hbLower
      _ = A^(τ+(1 : ℝ)/500) := by rw [← Real.rpow_sub hA0]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hA.le (by linarith only [hτmax])
  exact {
    mu_positive := hμ
    b_lt_T := hbT
    gap_cap := hcap
    pivot_lower := hbLower
    pivot_upper := hbUpper.trans (Real.rpow_le_rpow_of_exponent_le hA.le (by linarith only [hσmax]))
    pad_lower := hPLower
    pad_upper := hPUpper
    cap_ratio := hAT
    curvature := hμT
    mass_time := by linarith only [hmassTime,htime1]
    mass_pivot := hmassPivot
    mass_bound := hmass.trans (Real.rpow_le_rpow_of_exponent_le hA.le (by linarith only [hτmax]))
    time_bound := Real.rpow_le_rpow_of_exponent_le hA.le (by linarith only [hυmax])
    negative_charge := hE
  }

end
end StrongSilver
