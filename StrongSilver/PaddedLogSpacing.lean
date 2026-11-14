-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BalancedSplitMasses
import StrongSilver.FourPhaseLastRelativeError

namespace StrongSilver.PaddedSplitInput
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

theorem balanced_total_mass_ratio {S : PaddedSplitInput} {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4)
    (h : S.Balanced δ) : |S.z/(rho^2*S.t)-1| ≤ 5*δ := by
  have hden := mul_pos rho_positive S.t_positive
  have hden2 := mul_pos (pow_pos rho_positive 2) S.t_positive
  have hδ1 : δ ≤ 1 := hδmax.trans (by norm_num)
  have hLa := ratio_close_of_log_close (div_pos S.valid.1 hden) hδ hδ1 h.1
  have hRa := ratio_close_of_log_close (div_pos S.valid.2.1 hden) hδ hδ1 h.2.1
  have hLlo := (le_div_iff₀ hden).mp (show 1-2*δ ≤ S.a/(rho*S.t) by linarith only [(abs_le.mp hLa).1])
  have hLhi := (div_le_iff₀ hden).mp (show S.a/(rho*S.t) ≤ 1+2*δ by linarith only [(abs_le.mp hLa).2])
  have hRlo := (le_div_iff₀ hden).mp (show 1-2*δ ≤ S.b/(rho*S.t) by linarith only [(abs_le.mp hRa).1])
  have hRhi := (div_le_iff₀ hden).mp (show S.b/(rho*S.t) ≤ 1+2*δ by linarith only [(abs_le.mp hRa).2])
  have hL : |S.a-rho*S.t| ≤ 2*rho*δ*S.t :=
    abs_le.mpr ⟨by nlinarith only [hLlo],by nlinarith only [hLhi]⟩
  have hR : |S.b-rho*S.t| ≤ 2*rho*δ*S.t :=
    abs_le.mpr ⟨by nlinarith only [hRlo],by nlinarith only [hRhi]⟩
  have hd := (div_le_iff₀ S.t_positive).mp h.2.2
  have hreset := (balanced_drawdown_identity hδmax h).1
  have hcenter : S.z-rho^2*S.t = (S.a-rho*S.t)+(S.b-rho*S.t)-drawdown S.left := by
    rw [hreset,rho_square]
    ring
  have ht : |S.z-rho^2*S.t| ≤ (4*rho+1)*δ*S.t := by
    rw [hcenter]
    have ha := abs_sub_le ((S.a-rho*S.t)+(S.b-rho*S.t)) (0:ℝ) (drawdown S.left)
    simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg (drawdown_nonneg S.left)] at ha
    have hb := abs_add_le (S.a-rho*S.t) (S.b-rho*S.t)
    nlinarith only [ha,hb,hL,hR,hd]
  have hcoef : 4*rho+1 ≤ 5*rho^2 := by nlinarith only [rho_bounds.1,rho_square]
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hδ S.t_positive.le)
  have hid : S.z/(rho^2*S.t)-1 = (S.z-rho^2*S.t)/(rho^2*S.t) := by
    field_simp [rho_positive.ne',S.t_positive.ne'] <;> ring
  rw [hid,abs_div,abs_of_pos hden2]
  apply (div_le_iff₀ hden2).mpr
  nlinarith only [ht,hcoef']

theorem balanced_total_log_mass {S : PaddedSplitInput} {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100)
    (h : S.Balanced δ) : |Real.log S.z-(2*Real.log rho+Real.log S.t)| ≤ 10*δ := by
  have hr := balanced_total_mass_ratio hδ (hδmax.trans (by norm_num)) h
  have hhalf : 1/2 ≤ S.z/(rho^2*S.t) := by
    have hh := (abs_le.mp hr).1
    linarith only [hh,hδmax]
  have hl := (abs_log_le_twice_deviation hhalf).trans (mul_le_mul_of_nonneg_left hr (by norm_num))
  have hz := S.valid.1.trans_le S.valid.2.2.2.1
  rw [Real.log_div hz.ne' (mul_pos (pow_pos rho_positive 2) S.t_positive).ne',
    Real.log_mul (pow_pos rho_positive 2).ne' S.t_positive.ne',Real.log_pow] at hl
  simp only [Nat.cast_ofNat] at hl
  linarith only [hl]

/-- Logarithmic spacing (4.12) directly at the fixed padded heights.
The parent-child mass equality respects the terminal reserve convention. -/
theorem balanced_edge_log_spacing {parent child : PaddedSplitInput} {δ : ℝ}
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100) (hp : parent.Balanced δ) (hc : child.Balanced δ)
    (hchild : child.z = parent.a ∨ child.z = parent.b) :
    |Real.log parent.t-Real.log child.t-Real.log rho| ≤ 11*δ := by
  have hmass := balanced_total_log_mass hδ hδmax hc
  have hparent : |Real.log (child.z/(rho*parent.t))| ≤ δ := by
    rcases hchild with hchild | hchild
    · rw [hchild]; exact hp.1
    · rw [hchild]; exact hp.2.1
  rw [Real.log_div (child.valid.1.trans_le child.valid.2.2.2.1).ne'
    (mul_pos rho_positive parent.t_positive).ne',Real.log_mul rho_positive.ne' parent.t_positive.ne'] at hparent
  have hid : Real.log parent.t-Real.log child.t-Real.log rho =
      (Real.log child.z-(2*Real.log rho+Real.log child.t))-
      (Real.log child.z-(Real.log rho+Real.log parent.t)) := by ring
  rw [hid]
  exact (abs_sub_le (Real.log child.z-(2*Real.log rho+Real.log child.t)) (0:ℝ)
    (Real.log child.z-(Real.log rho+Real.log parent.t))).trans (by
    simp only [sub_zero,zero_sub,abs_neg]
    linarith only [hmass,hparent])

end
end StrongSilver.PaddedSplitInput
