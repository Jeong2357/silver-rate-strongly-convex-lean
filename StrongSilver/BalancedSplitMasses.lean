-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SilverOffsetBalance
import StrongSilver.PaddedSplitInput
import StrongSilver.VisibilityLogDeficit
import StrongSilver.FinitePaddedCharges

namespace StrongSilver.PaddedSplitInput
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3200000

/-- Absolute mass comparisons at a balanced original signed split. -/
theorem balanced_mass_bounds {S : PaddedSplitInput} {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4)
    (h : S.Balanced δ) : S.t ≤ S.a ∧ S.a ≤ 5*S.t ∧ S.t ≤ S.b ∧ S.b ≤ 5*S.t ∧
      S.t ≤ S.z ∧ S.z ≤ 11*S.t := by
  have ht := S.t_positive
  have hden := mul_pos rho_positive ht
  have hδ1 : δ ≤ 1 := hδmax.trans (by norm_num)
  have hL := ratio_close_of_log_close (div_pos S.valid.1 hden) hδ hδ1 h.1
  have hR := ratio_close_of_log_close (div_pos S.valid.2.1 hden) hδ hδ1 h.2.1
  have hLlo : 1/2 ≤ S.a/(rho*S.t) := by have hh := (abs_le.mp hL).1; linarith only [hh,hδmax]
  have hLhi : S.a/(rho*S.t) ≤ 3/2 := by have hh := (abs_le.mp hL).2; linarith only [hh,hδmax]
  have hRlo : 1/2 ≤ S.b/(rho*S.t) := by have hh := (abs_le.mp hR).1; linarith only [hh,hδmax]
  have hRhi : S.b/(rho*S.t) ≤ 3/2 := by have hh := (abs_le.mp hR).2; linarith only [hh,hδmax]
  have hLa := (le_div_iff₀ hden).mp hLlo
  have hLb := (div_le_iff₀ hden).mp hLhi
  have hRa := (le_div_iff₀ hden).mp hRlo
  have hRb := (div_le_iff₀ hden).mp hRhi
  have hrholo := mul_lt_mul_of_pos_right rho_bounds.1 ht
  have hrhohi := mul_lt_mul_of_pos_right rho_bounds.2 ht
  have ha : S.t ≤ S.a := by linarith only [hLa,hrholo]
  have hb : S.t ≤ S.b := by linarith only [hRa,hrholo]
  have ha5 : S.a ≤ 5*S.t := by linarith only [hLb,hrhohi,ht]
  have hb5 : S.b ≤ 5*S.t := by linarith only [hRb,hrhohi,ht]
  exact ⟨ha,ha5,hb,hb5,ha.trans S.valid.2.2.2.1,by linarith only [ha5,hb5,S.valid.2.2.2.2.1]⟩

theorem balanced_drawdown_identity {S : PaddedSplitInput} {δ : ℝ} (hδmax : δ ≤ 1/4)
    (h : S.Balanced δ) : S.z = S.a+S.b+S.t-drawdown S.left ∧ 3*S.t/4 ≤ S.t-drawdown S.left := by
  have hd := (div_le_iff₀ S.t_positive).mp h.2.2
  have hdt : drawdown S.left ≤ S.t := by nlinarith only [hd,hδmax,S.t_positive]
  have hdef := S.valid.2.2.2.2.2
  rw [min_eq_left (hdt.trans S.pivot_right_ge_time)] at hdef
  exact ⟨by linarith only [hdef],by nlinarith only [hd,hδmax,S.t_positive]⟩

/-- Terminal vertices in a window of times much smaller than κ cannot
be balanced, since the right mass retains the entire terminal reserve. -/
theorem terminal_unbalanced {S : PaddedSplitInput} {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4)
    (hsmall : 5*S.t < S.reserve) : ¬ S.Balanced δ := by
  intro h
  have hb := (balanced_mass_bounds hδ hδmax h).2.2.2.1
  have hr : S.reserve ≤ S.b := by
    unfold b
    linarith only [prefixMax_nonneg S.right,S.pad_positive]
  linarith only [hb,hr,hsmall]

/-- At a balanced split failing the good test, either the left drawdown
or the visible positive-minus-prefix logarithm pays a linear δ charge. -/
theorem balanced_negative_failure_visible {S : PaddedSplitInput} {δ : ℝ}
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4) (h : S.Balanced δ)
    (hbad : δ*S.t < negativeMass S.left) :
    δ*S.t/2 < drawdown S.left ∨
      δ/23 ≤ Real.log (1+(positiveMass (S.left++S.pivot::S.right)-prefixMax (S.left++S.pivot::S.right))/S.z) := by
  rcases negative_mass_failure hbad with hd | hd
  · exact Or.inl hd
  · apply Or.inr
    have hparent := visible_parent_deficit S.left S.right S.pivot
    have hdef0 : 0 ≤ positiveMass (S.left++S.pivot::S.right)-prefixMax (S.left++S.pivot::S.right) :=
      sub_nonneg.mpr (prefixMax_le_positiveMass _)
    have hz := balanced_mass_bounds hδ hδmax h
    simpa only [show (2:ℝ)*11+1 = 23 by norm_num] using
      visibility_log_deficit hδ (hδmax.trans (by norm_num)) S.t_positive (S.valid.1.trans_le S.valid.2.2.2.1)
        hdef0 (by norm_num : (0:ℝ) < 11) hz.2.2.2.2.2 (hd.le.trans hparent)

end
end StrongSilver.PaddedSplitInput
