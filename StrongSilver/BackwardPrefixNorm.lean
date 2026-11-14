-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BackwardNormAnyPath

namespace StrongSilver
open Real
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
set_option maxHeartbeats 1000000

theorem inverseCharge_append (μ : ℝ) (h k : List ℝ) :
    inverseCharge μ (h++k) = inverseCharge μ h+inverseCharge μ k := by
  simp only [inverseCharge,List.map_append,List.sum_append]

theorem smallPositiveSum_append (μ : ℝ) (h k : List ℝ) :
    smallPositiveSum μ (h++k) = smallPositiveSum μ h+smallPositiveSum μ k := by
  simp only [smallPositiveSum,List.map_append,List.sum_append]

theorem inverseCharge_drop_le (μ : ℝ) (h : List ℝ) (i : ℕ) :
    inverseCharge μ (h.drop i) ≤ inverseCharge μ h := by
  have hh := inverseCharge_append μ (h.take i) (h.drop i)
  rw [List.take_append_drop] at hh
  linarith only [hh,inverseCharge_nonneg μ (h.take i)]

theorem smallPositiveSum_drop_le (μ : ℝ) (h : List ℝ) (i : ℕ) :
    smallPositiveSum μ (h.drop i) ≤ smallPositiveSum μ h := by
  have hh := smallPositiveSum_append μ (h.take i) (h.drop i)
  rw [List.take_append_drop] at hh
  linarith only [hh,smallPositiveSum_nonneg μ (h.take i)]

theorem backward_norm_all_prefixes {μ M : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hM : 0 ≤ M)
    (g : V → V) (hginner : ∀ x, 0 ≤ inner ℝ (g x) x) (hgbound : ∀ x, ‖g x‖ ≤ M)
    (h : List ℝ) (hcritical : ∀ b ∈ h, 1-μ*b ≠ 0) (x y : V)
    (hend : iterate h (stronglyConvexGradient μ g) x = y) (i : ℕ) :
    ‖iterate (h.take i) (stronglyConvexGradient μ g) x‖ ≤
      Real.exp (inverseCharge μ h)*(‖y‖+(1-μ)*M*smallPositiveSum μ h) := by
  have hrun : iterate (h.drop i) (stronglyConvexGradient μ g)
      (iterate (h.take i) (stronglyConvexGradient μ g) x) = y := by
    rw [← iterate_append,List.take_append_drop,hend]
  have hh := backward_norm_of_iterate hμ hμ1 hM g hginner hgbound (h.drop i)
    (fun b hb => hcritical b (List.mem_of_mem_drop hb)) _ y hrun
  have he := Real.exp_le_exp.mpr (inverseCharge_drop_le μ h i)
  have hcoef : 0 ≤ (1-μ)*M := mul_nonneg (sub_nonneg.mpr hμ1) hM
  have hs := mul_le_mul_of_nonneg_left (smallPositiveSum_drop_le μ h i) hcoef
  have hbracket : 0 ≤ ‖y‖+(1-μ)*M*smallPositiveSum μ (h.drop i) := by
    exact add_nonneg (norm_nonneg _) (mul_nonneg hcoef (smallPositiveSum_nonneg _ _))
  exact hh.trans (mul_le_mul he (by linarith only [hs]) hbracket (Real.exp_pos _).le)

end
end StrongSilver
