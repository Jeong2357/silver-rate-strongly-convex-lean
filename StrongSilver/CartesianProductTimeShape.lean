-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianGroupMassShape
import StrongSilver.FourPhaseErrorBudgets

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2800000

def internalExcesses (G : FourGapGroup) (φ : ℝ → ℝ) : Fin 3 → ℝ :=
  ![adjustedExcess φ G.first G.leftPivot,adjustedExcess φ G.left G.middlePivot,
    adjustedExcess φ G.third G.rightPivot]

theorem transformed_gap_mass (G : FourGapGroup) {μ : ℝ} (hμ : 0 < μ) (b : ℝ)
    (hsmall : μ*absoluteMass (boundedWord G.gaps (G.pivots b)) ≤ 1/4) (i : Fin 4) :
    transformedGapMaximum μ (G.gaps i)+1 =
      ![G.first.prefixMass (logarithmicStep μ),G.second.prefixMass (logarithmicStep μ),
        G.third.prefixMass (logarithmicStep μ),G.fourth.prefixMass (logarithmicStep μ)] i := by
  have hm := transformed_prefix_max hμ (G.gaps i)
    (gap_small_steps hμ.le G.gaps (G.pivots b) hsmall i)
  change prefixMax ((G.gaps i).map (logarithmicStep μ)) = transformedGapMaximum μ (G.gaps i) at hm
  rw [← hm]
  fin_cases i <;> rfl

theorem phase_excess_exact (G : FourGapGroup) {μ : ℝ} (hμ : 0 < μ) (b : ℝ)
    (hsmall : μ*absoluteMass (boundedWord G.gaps (G.pivots b)) ≤ 1/4)
    (hKL : 0 < adjustedExcess (logarithmicStep μ) G.first G.leftPivot) (i : Fin 3) :
    phaseDuration μ G.gaps (G.pivots b) i-(transformedGapMaximum μ (G.gaps i.castSucc)+1) =
      G.internalExcesses (logarithmicStep μ) i := by
  rw [phaseDuration_minus_mass hμ G.gaps (G.pivots b) hsmall i]
  have hd := (positive_excess_mass_identity (logarithmicStep μ) G.first G.second G.leftPivot hKL).2
  change gapDrawdown (logarithmicStep μ) G.left = _ at hd
  fin_cases i
  · rfl
  · change logarithmicStep μ G.middlePivot-1-G.second.gapDrawdown (logarithmicStep μ) =
      logarithmicStep μ G.middlePivot-1-G.left.gapDrawdown (logarithmicStep μ)
    rw [hd]
  · rfl

/-- Division by the positive scale turns an unscaled mass error into a
coordinate error without introducing an additional approximation. -/
theorem scaled_coordinate_error {T a m E : ℝ} (hT : 0 < T)
    (h : |T*a-m| ≤ E*T^2) : |a-m/T| ≤ E*T := by
  have he : T*(a-m/T) = T*a-m := by field_simp
  have hh : T*|a-m/T| = |T*a-m| := by
    rw [← abs_of_pos hT,← abs_mul,abs_of_pos hT,he]
  have hb : T*|a-m/T| ≤ T*(E*T) := by
    rw [hh]
    nlinarith only [h]
  exact (mul_le_mul_iff_right₀ hT).mp hb

/-- Exact original product-time coordinates and exact Cartesian mass
coordinates differ by O(mu*T) on a uniformly bounded group. -/
theorem productShape_massShape_error (G : FourGapGroup) {μ K T b : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hK : 1 ≤ K) (hT : 1 ≤ T)
    (hsmall : μ*absoluteMass (boundedWord G.gaps (G.pivots b)) ≤ 1/4)
    (hscale : μ*(K*T) ≤ 1)
    (hKL : 0 < adjustedExcess (logarithmicStep μ) G.first G.leftPivot)
    (hmass : ∀ i, transformedGapMaximum μ (G.gaps i)+1 ≤ K*T)
    (htime : ∀ i, |phaseDuration μ G.gaps (G.pivots b) i| ≤ K*T)
    (habsolute : absoluteMass (boundedWord G.gaps (G.pivots b)) ≤ K*T) :
    ∀ j, |productShape μ T G.gaps (G.pivots b) 0 j-G.massShape (logarithmicStep μ) T j| ≤
      (12*K^2+2*K)*μ*T := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hKpos : 0 ≤ K := zero_le_one.trans hK
  have hN := absoluteMass_nonnegative (boundedWord G.gaps (G.pivots b))
  have hmassSmall (i : Fin 4) : μ*transformedGapMaximum μ (G.gaps i) ≤ 1 := by
    have hp := mul_le_mul_of_nonneg_left (hmass i) hμ.le
    nlinarith only [hp,hscale,hμ]
  have htimeSmall (i : Fin 3) : |μ*phaseDuration μ G.gaps (G.pivots b) i| ≤ 1 := by
    rw [abs_mul,abs_of_pos hμ]
    exact (mul_le_mul_of_nonneg_left (htime i) hμ.le).trans hscale
  have hm (i : Fin 4) : |normalizedMass μ T G.gaps (G.pivots b) i-
      ![G.first.prefixMass (logarithmicStep μ),G.second.prefixMass (logarithmicStep μ),
        G.third.prefixMass (logarithmicStep μ),G.fourth.prefixMass (logarithmicStep μ)] i/T| ≤
        (12*K^2+2*K)*μ*T := by
    have h := actual_normalized_mass_error hμ hTpos G.gaps (G.pivots b) hsmall i (hmassSmall i)
    have hb := mass_error_budget_scaled hμ.le hK hT
      (transformedGapMaximum_nonnegative hμ (G.gaps i) (gap_small_steps hμ.le G.gaps (G.pivots b) hsmall i))
      hN (hmass i) habsolute
    have hprice : 6*K^2*μ*T^2 ≤ ((12*K^2+2*K)*μ)*T^2 := by
      have hq := mul_nonneg (sq_nonneg K) (mul_nonneg hμ.le (sq_nonneg T))
      have hk := mul_nonneg hKpos (mul_nonneg hμ.le (sq_nonneg T))
      nlinarith only [hq,hk]
    have herr := h.trans (hb.trans hprice)
    rw [G.transformed_gap_mass hμ b hsmall i] at herr
    simpa only [mul_assoc] using scaled_coordinate_error hTpos herr
  have hk (i : Fin 3) : |normalizedExcess μ T G.gaps (G.pivots b) i-
      G.internalExcesses (logarithmicStep μ) i/T| ≤ (12*K^2+2*K)*μ*T := by
    have h := actual_normalized_excess_error hμ hμ1 hTpos G.gaps (G.pivots b) hsmall 0 i
      (hmassSmall i.castSucc) (htimeSmall i)
    rw [G.phase_excess_exact hμ b hsmall hKL i] at h
    have hb := actual_error_budgets_scaled hμ hK hT G.gaps (G.pivots b) hsmall i
      (hmass i.castSucc) (htime i) habsolute
    have hh : |T*normalizedExcess μ T G.gaps (G.pivots b) i-
      G.internalExcesses (logarithmicStep μ) i| ≤ ((12*K^2+2*K)*μ)*T^2 := by
      simpa only [mul_assoc] using h.trans hb
    simpa only [mul_assoc] using scaled_coordinate_error hTpos hh
  intro j
  fin_cases j
  · exact hm 0
  · exact hm 1
  · exact hm 2
  · exact hm 3
  · exact hk 0
  · exact hk 1
  · exact hk 2
  · change |(0:ℝ)-0| ≤ _
    have hE : 0 ≤ 12*K^2+2*K := by nlinarith only [sq_nonneg K,hKpos]
    simpa using mul_nonneg (mul_nonneg hE hμ.le) hTpos.le

end
end StrongSilver.ScheduleTree.FourGapGroup
