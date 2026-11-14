-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarRampEstimates

namespace StrongSilver
open Set Real
noncomputable section
set_option maxHeartbeats 1000000

theorem positive_trajectory_suffix (h : List ℝ) (G : ℝ → ℝ) (x e : ℝ) (he : 0 < e)
    (hend : iterate h G x = e)
    (hstates : ∀ k : ℕ, k ≤ h.length → 0 < iterate (h.take k) G x) (i : ℕ) :
    iterate (h.drop i) G (iterate (h.take i) G x) = e ∧
      ∀ j : ℕ, j ≤ (h.drop i).length → 0 < iterate ((h.drop i).take j) G (iterate (h.take i) G x) := by
  have hall (k : ℕ) : 0 < iterate (h.take k) G x := by
    by_cases hk : k ≤ h.length
    · exact hstates k hk
    · rw [List.take_of_length_le (by omega),hend]
      exact he
  constructor
  · rw [← iterate_append,List.take_append_drop,hend]
  · intro j hj
    rw [← iterate_append,← List.take_add]
    exact hall (i+j)

theorem positiveMass_drop_le (h : List ℝ) (i : ℕ) :
    Scalar.SignedIntervals.positiveMass (h.drop i) ≤ Scalar.SignedIntervals.positiveMass h := by
  have hh := Scalar.SignedIntervals.positiveMass_append (h.take i) (h.drop i)
  rw [List.take_append_drop] at hh
  linarith only [hh,Scalar.SignedIntervals.positiveMass_nonneg (h.take i)]

theorem negativeLogSum_nonnegative {T : ℝ} (hT : 0 < T) (h : List ℝ) : 0 ≤ negativeLogSum h T := by
  apply List.sum_nonneg
  intro y hy
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
  split_ifs
  · exact Real.log_nonneg (le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hT.le))
  · exact le_rfl

theorem negativeLogSum_drop_le {T : ℝ} (hT : 0 < T) (h : List ℝ) (i : ℕ) :
    negativeLogSum (h.drop i) T ≤ negativeLogSum h T := by
  have hh : negativeLogSum h T = negativeLogSum (h.take i) T+negativeLogSum (h.drop i) T := by
    conv_lhs => rw [← List.take_append_drop i h]
    simp only [negativeLogSum,List.map_append,List.sum_append]
  linarith only [hh,negativeLogSum_nonnegative hT (h.take i)]

theorem scalarRampGrowth_drop_le {T A b : ℝ} (hT : 0 < T) (hb : 0 < b) (hAT : A < T)
    (h : List ℝ) (i : ℕ) : scalarRampGrowth T A b (h.drop i) ≤ scalarRampGrowth T A b h := by
  have hmass := positiveMass_drop_le h i
  have hden : 0 < T*(1-A/T) := by
    apply mul_pos hT
    have hh := (div_lt_one hT).mpr hAT
    linarith
  have he := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hmass hden.le)
  have hf := div_le_div_of_nonneg_right hmass hb.le
  unfold scalarRampGrowth
  apply mul_le_mul he (add_le_add le_rfl hf)
    (add_nonneg zero_le_one (div_nonneg (Scalar.SignedIntervals.positiveMass_nonneg (h.drop i)) hb.le))
    (Real.exp_pos _).le

end
end StrongSilver
