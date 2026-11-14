-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TraceExceptional
import StrongSilver.TraceLogPrices
import StrongSilver.NoLeftTerminal

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

/-- A block beginning at the first step needs no positive source gate.
Its suffix is preserved by the same actual cone construction. -/
theorem eventually_working_open_block_distance_lower : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ c : ℝ, ∀ I s : List ℝ, ∀ r : ℝ,
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → 2 ≤ c → c ≤ A^(2 : ℝ) → 1/32 ≤ 1-μ*c →
      (∀ a ∈ I, 1-μ*a ≠ 0) →
      PositiveTrace μ s (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ)) r →
      ENNReal.ofReal (r/(workingBlockFactor A μ I)^2) ≤ D κ ((I++[c])++s) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_working_cone_size] with A hA hsize
  intro κ μ c I s r hκ hμ hμ1 hc hcA hqc hcritical S
  have hA0 := zero_lt_one.trans_le hA
  have hκ0 := zero_lt_one.trans_le hκ
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hV : 0 < ‖S.path.x 0‖ := norm_pos_iff.mpr S.nonzero
  have hM : 1 ≤ A^(10 : ℝ) := Real.one_le_rpow hA (by norm_num)
  have hH : 0 ≤ A^(10 : ℝ)*‖S.path.x 0‖ := by positivity
  have hη : 0 < workingGateFraction A := Real.rpow_pos_of_pos hA0 _
  have hη1 : workingGateFraction A ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num)
  have hminus : S.path.family.Gate (S.path.x 0) (-workingGateFraction A) :=
    S.path.family.gate_below S.positive.2 S.gate (by linarith only [hη])
  obtain ⟨C,n,Q,hQ,hN,hend,hsteps,hz,hg⟩ := two_cone_attachment hμ0 hc (by linarith only [hqc]) hV hM hH hη hη1
    I hcritical S.path (unitDirection (S.path.x 0)) (unitDirection_inner S.nonzero) (norm_smul_unitDirection S.nonzero).symm
    (fun j => (S.projections j).1) (fun j => (S.projections j).2) S.gate hminus
  have hC := hsize μ c ‖S.path.x 0‖ hμ0.le (by linarith only [hc]) hcA hV hqc C
  have htrace := C.traceRadius_bound_of_size hμ0.le hC.1 hC.2 I
  have hNfactor : ‖Q.x 0‖ ≤ workingBlockFactor A μ I*‖S.path.x 0‖ := by
    calc
      _ ≤ A^(14 : ℝ)*‖S.path.x 0‖*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I) := hN.trans htrace
      _ ≤ A^(25 : ℝ)*‖S.path.x 0‖*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I) := by
        have hp : A^(14 : ℝ) ≤ A^(25 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
        have hs : 0 ≤ 1+smallPositiveSum μ I := by linarith only [smallPositiveSum_nonneg μ I]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) (Real.exp_pos _).le) hs
      _ = _ := by unfold workingBlockFactor; ring
  have hEndNorm : ‖Q.x (Fin.last n)‖ = ‖S.path.x (Fin.last S.length)‖ := by
    rw [hend]
    exact retainedIsometry.norm_map _
  have hractual := ratio_lower_of_source_scale hV (norm_pos_iff.mpr hQ) (workingBlockFactor_positive hA0 μ I)
    (norm_nonneg (S.path.x (Fin.last S.length))) hEndNorm.symm.le hNfactor
  have hratio := (div_le_div_of_nonneg_right S.ratio (sq_nonneg (workingBlockFactor A μ I))).trans hractual
  have hh := (ENNReal.ofReal_le_ofReal hratio).trans (Q.finite_distance_lower hκ hμ hμ1 hQ)
  have hsteps' := hsteps.trans (congrArg (fun l : List ℝ => (I++[c])++l) S.steps_eq)
  simpa only [hsteps'] using hh

theorem open_terminal_distance_lower {κ μ c A : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) (hc : 2 ≤ c) (hqc : 1/32 ≤ 1-μ*c)
    (hcap : μ*A ≤ 1/2) (I t : List ℝ) (hcritical : ∀ b ∈ I, 1-μ*b ≠ 0)
    (ht : ∀ b ∈ t, 0 < b → b ≤ A) :
    ENNReal.ofReal (Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))/
      ((4*(1200000 : ℝ)^2)*(Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I))^2)) ≤ D κ ((I++[c])++t) := by
  have hμ0 : 0 < μ := (one_div_pos.mpr (zero_lt_one.trans_le hκ)).trans_le hμ
  obtain ⟨n,Q,hQ,hsteps,hend,hratio⟩ := terminal_connector_ratio hμ0 hc hqc (κ := 1) (K := 1) zero_lt_one le_rfl
    (by linarith only [hc]) hcap I t hcritical ht (Y := (1 : ℝ)) one_ne_zero
  have hh := (ENNReal.ofReal_le_ofReal hratio).trans (Q.finite_distance_lower hκ hμ hμ1 hQ)
  simpa only [hsteps,mul_one,div_one] using hh

theorem open_scalar_distance_lower {κ μ A : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) (hcap : μ*A ≤ 1/2)
    (I t : List ℝ) (hcritical : ∀ b ∈ I, 1-μ*b ≠ 0) (ht : ∀ b ∈ t, 0 < b → b ≤ A) :
    ENNReal.ofReal (Real.exp (-2*(inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t))) ≤ D κ (I++t) := by
  have hμ0 : 0 < μ := (one_div_pos.mpr (zero_lt_one.trans_le hκ)).trans_le hμ
  obtain ⟨Q,hsteps,hend,hQ,hratio⟩ := normalized_terminal_ratio hμ0 hμ1 hcap I t hcritical ht (Y := (1 : ℝ)) one_ne_zero
  have hh := (ENNReal.ofReal_le_ofReal hratio).trans (Q.finite_distance_lower hκ hμ hμ1 hQ)
  simpa only [hsteps] using hh

end
end StrongSilver
