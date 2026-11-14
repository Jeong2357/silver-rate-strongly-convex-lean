-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarGapNorm
import StrongSilver.ScalarRampBudgets

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem logarithmicStep_upper {μ A b : ℝ} (hμ : 0 < μ) (hμA : μ*A < 1)
    (hb : 0 < b) (hbA : b ≤ A) : logarithmicStep μ b ≤ b/(1-μ*A) := by
  have hmul := mul_le_mul_of_nonneg_left hbA hμ.le
  have hd : 0 < 1-μ*b := by linarith
  have hdA : 0 < 1-μ*A := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [Real.log_inv] at hlog
  have he : (1-μ*b)⁻¹-1 = μ*b/(1-μ*b) := by field_simp [hd.ne']; ring
  rw [he] at hlog
  have hf : μ*b/(1-μ*b) ≤ μ*b/(1-μ*A) := by gcongr
  unfold logarithmicStep
  apply (div_le_iff₀ hμ).mpr
  have hh : b/(1-μ*A)*μ = μ*b/(1-μ*A) := by ring
  rw [hh]
  exact hlog.trans hf

theorem logarithmicStep_positive_part_upper {μ A b : ℝ} (hμ : 0 < μ) (hμA : μ*A < 1)
    (hbA : 0 < b → b ≤ A) : max (logarithmicStep μ b) 0 ≤ max b 0/(1-μ*A) := by
  by_cases hb : 0 < b
  · have hbμ : μ*b < 1 := (mul_le_mul_of_nonneg_left (hbA hb) hμ.le).trans_lt hμA
    rw [max_eq_left (logarithmicStep_pos hμ hb hbμ).le,max_eq_left hb.le]
    exact logarithmicStep_upper hμ hμA hb (hbA hb)
  · have hneg := logarithmicStep_nonpos hμ (le_of_not_gt hb)
    rw [max_eq_right hneg,max_eq_right (le_of_not_gt hb),zero_div]

theorem logarithmicSteps_positive_mass_upper {μ A : ℝ} (hμ : 0 < μ) (hμA : μ*A < 1)
    (h : List ℝ) (hh : ∀ b ∈ h, 0 < b → b ≤ A) :
    Scalar.SignedIntervals.positiveMass (h.map (logarithmicStep μ)) ≤
      Scalar.SignedIntervals.positiveMass h/(1-μ*A) := by
  induction h with
  | nil => simp [Scalar.SignedIntervals.positiveMass]
  | cons b h ih =>
    have hb := logarithmicStep_positive_part_upper hμ hμA (hh b List.mem_cons_self)
    have ht := ih (fun c hc => hh c (List.mem_cons_of_mem b hc))
    simp only [List.map_cons,Scalar.SignedIntervals.positiveMass,List.sum_cons] at *
    calc
      _ ≤ max b 0/(1-μ*A)+((h.map fun x => max x 0).sum)/(1-μ*A) := add_le_add hb ht
      _ = _ := by ring

theorem transformedGapMaximum_le_positive_mass {μ A : ℝ} (hμ : 0 < μ) (hμA : μ*A < 1)
    (h : List ℝ) (hh : ∀ b ∈ h, 0 < b → b ≤ A) :
    transformedGapMaximum μ h ≤ Scalar.SignedIntervals.positiveMass h/(1-μ*A) := by
  have hsmall : ∀ b ∈ h, μ*b < 1 := by
    intro b hb
    by_cases hbp : 0 < b
    · exact (mul_le_mul_of_nonneg_left (hh b hb hbp) hμ.le).trans_lt hμA
    · have hm := mul_nonpos_of_nonneg_of_nonpos hμ.le (le_of_not_gt hbp)
      linarith only [hm]
  have hp := Scalar.SignedIntervals.prefixMax_le_positiveMass (h.map (logarithmicStep μ))
  rw [transformed_prefix_max hμ h hsmall] at hp
  exact hp.trans (logarithmicSteps_positive_mass_upper hμ hμA h hh)

end
end StrongSilver
