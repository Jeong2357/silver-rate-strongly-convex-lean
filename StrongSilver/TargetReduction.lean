-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Counterexamples
import StrongSilver.LogConsequences

namespace StrongSilver
noncomputable section

/-- The scalar reduction in Section 2.1. The remaining geometric argument must
prove `WeightedCountBound`; this conditional lemma does not assert that result. -/
theorem distance_lower_bound_of_weighted_count_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hcount : WeightedCountBound a) : DistanceLowerBound := by
  obtain ⟨C0,hC0,hlog⟩ := distance_log_rank_bound
  obtain ⟨K,C1,hK,hC1,hcount⟩ := hcount
  let C := 2*C0*a^(-nu)*C1
  let κ₀ := max K (max (4/a) 2)
  have hC : 0 < C := mul_pos (mul_pos (mul_pos (by norm_num) hC0)
    (Real.rpow_pos_of_pos ha _)) hC1
  have hk02 : (2 : ℝ) ≤ κ₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hk0pos : 0 < κ₀ := lt_of_lt_of_le (by norm_num) hk02
  refine ⟨C,κ₀,hC,hk0pos,fun κ hk h => ?_⟩
  have hk2 : (2 : ℝ) ≤ κ := hk02.trans hk
  have hk1 : 1 ≤ κ := by linarith
  have hkstrict : 1 < κ := by linarith
  have hkpos : 0 < κ := by linarith
  have h4a : 4/a ≤ κ := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hcap : 4 ≤ a*κ := by
    have hh := (div_le_iff₀ ha).mp h4a
    simpa only [mul_comm] using hh
  by_cases hn : h.length = 0
  · have hh : h = [] := List.length_eq_zero_iff.mp hn
    subst h
    simp [D_nil hk1]
  · by_cases hD : D κ h ≤ 1
    · have hW := hcount κ ((le_max_left _ _).trans hk) h (by omega) hD
      have hL := hlog κ a hkstrict ha ha1 hcap h
      have hcoef : 0 ≤ (2*C0*a^(-nu))*κ^(-nu) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0.le)
          (Real.rpow_nonneg ha.le _)) (Real.rpow_nonneg hkpos.le _)
      have hprod := mul_le_mul_of_nonneg_left hW hcoef
      have hLb : -Real.log (D κ h).toReal ≤ C*(h.length : ℝ)*κ^(-nu) := by
        dsimp [C]
        nlinarith only [hL,hprod]
      have hDpositive : 0 < (D κ h).toReal :=
        ENNReal.toReal_pos (errors_positive hkstrict h).1.ne' (D_ne_top κ h)
      apply (ENNReal.ofReal_le_iff_le_toReal (D_ne_top κ h)).mpr
      have he := Real.exp_le_exp.mpr (show -C*(h.length : ℝ)*κ^(-nu) ≤
        Real.log (D κ h).toReal by linarith only [hLb])
      rwa [Real.exp_log hDpositive] at he
    · have hexp : Real.exp (-C*(h.length : ℝ)*κ^(-nu)) ≤ 1 := by
        have hn0 : -C*(h.length : ℝ)*κ^(-nu) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC.le) (Nat.cast_nonneg _))
            (Real.rpow_nonneg hkpos.le _)
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hn0
      have he : ENNReal.ofReal (Real.exp (-C*(h.length : ℝ)*κ^(-nu))) ≤ 1 := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hexp
      exact he.trans (le_of_not_ge hD)

/-- Conditional target reduction; the hypothesis is still to be discharged by
the trajectory and band argument. -/
theorem main_lower_bound_of_weighted_count_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hcount : WeightedCountBound a) : MainLowerBound :=
  main_iff_distance_lower.mpr (distance_lower_bound_of_weighted_count_bound ha ha1 hcount)

end
end StrongSilver
