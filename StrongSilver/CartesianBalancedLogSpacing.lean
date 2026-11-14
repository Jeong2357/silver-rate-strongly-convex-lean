-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianBalancedScales
import StrongSilver.FourPhaseLastRelativeError

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3600000

theorem balanced_total_mass_ratio {φ : ℝ → ℝ} {ε : ℝ} {l r : ScheduleTree} {b : ℝ}
    (hε : ε < 1) (h : SilverBalanced φ ε (.split l b r)) :
    |prefixMass φ (.split l b r)/(rho^2*φ b)-1| ≤ ε := by
  have hK := FourGapGroup.positive_excess_of_balance h hε
  have hm := (positive_excess_mass_identity φ l r b hK).1
  have hden := mul_pos rho_positive h.1
  have hden2 := mul_pos (pow_pos rho_positive 2) h.1
  have hL := abs_le.mp h.2.1
  have hR := abs_le.mp h.2.2.1
  have hk := abs_le.mp h.2.2.2
  have hLlo := (le_div_iff₀ hden).mp (show 1-ε ≤ l.prefixMass φ/(rho*φ b) by linarith only [hL.1])
  have hLhi := (div_le_iff₀ hden).mp (show l.prefixMass φ/(rho*φ b) ≤ 1+ε by linarith only [hL.2])
  have hRlo := (le_div_iff₀ hden).mp (show 1-ε ≤ r.prefixMass φ/(rho*φ b) by linarith only [hR.1])
  have hRhi := (div_le_iff₀ hden).mp (show r.prefixMass φ/(rho*φ b) ≤ 1+ε by linarith only [hR.2])
  have hKlo := (le_div_iff₀ h.1).mp (show 1-ε ≤ adjustedExcess φ l b/φ b by linarith only [hk.1])
  have hKhi := (div_le_iff₀ h.1).mp (show adjustedExcess φ l b/φ b ≤ 1+ε by linarith only [hk.2])
  have he : rho^2*φ b = (2*rho+1)*φ b := by rw [rho_square]
  have hlo : (1-ε)*(rho^2*φ b) ≤ prefixMass φ (.split l b r) := by
    rw [he]
    nlinarith only [hm,hLlo,hRlo,hKlo]
  have hhi : prefixMass φ (.split l b r) ≤ (1+ε)*(rho^2*φ b) := by
    rw [he]
    nlinarith only [hm,hLhi,hRhi,hKhi]
  have hdlo := (le_div_iff₀ hden2).mpr hlo
  have hdhi := (div_le_iff₀ hden2).mpr hhi
  exact abs_le.mpr ⟨by linarith only [hdlo],by linarith only [hdhi]⟩

theorem balanced_total_log_mass {φ : ℝ → ℝ} {ε : ℝ} {l r : ScheduleTree} {b : ℝ}
    (hε : ε ≤ 1/2) (h : SilverBalanced φ ε (.split l b r)) :
    |Real.log (prefixMass φ (.split l b r))-(2*Real.log rho+Real.log (φ b))| ≤ 2*ε := by
  have hr := balanced_total_mass_ratio (hε.trans_lt (by norm_num)) h
  have hhalf : 1/2 ≤ prefixMass φ (.split l b r)/(rho^2*φ b) := by
    have hh := (abs_le.mp hr).1
    linarith only [hh,hε]
  have hl := (abs_log_le_twice_deviation hhalf).trans (mul_le_mul_of_nonneg_left hr (by norm_num))
  rw [Real.log_div (prefixMass_positive φ _).ne' (mul_pos (pow_pos rho_positive _) h.1).ne',
    Real.log_mul (pow_pos rho_positive _).ne' h.1.ne',Real.log_pow] at hl
  simpa only [Nat.cast_ofNat] using hl

/-- Consecutive balanced splits have silver logarithmic spacing. This
finite estimate supplies the height and weighted depth comparisons in
the forest arguments of Sections 4.3--4.6. -/
theorem balanced_edge_log_spacing {φ : ℝ → ℝ} {ε parent : ℝ} {l r : ScheduleTree} {b : ℝ}
    (hε : ε ≤ 1/2) (hp : 0 < parent) (h : SilverBalanced φ ε (.split l b r))
    (hparent : |prefixMass φ (.split l b r)/(rho*parent)-1| ≤ ε) :
    |Real.log parent-Real.log (φ b)-Real.log rho| ≤ 4*ε := by
  have hchild := balanced_total_log_mass hε h
  have hhalf : 1/2 ≤ prefixMass φ (.split l b r)/(rho*parent) := by
    have hh := (abs_le.mp hparent).1
    linarith only [hh,hε]
  have hlog := (abs_log_le_twice_deviation hhalf).trans (mul_le_mul_of_nonneg_left hparent (by norm_num))
  rw [Real.log_div (prefixMass_positive φ _).ne' (mul_pos rho_positive hp).ne',
    Real.log_mul rho_positive.ne' hp.ne'] at hlog
  have he : Real.log parent-Real.log (φ b)-Real.log rho =
      (Real.log (prefixMass φ (.split l b r))-(2*Real.log rho+Real.log (φ b)))-
      (Real.log (prefixMass φ (.split l b r))-(Real.log rho+Real.log parent)) := by ring
  rw [he,sub_eq_add_neg]
  exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith only [hchild,hlog])

end
end StrongSilver.ScheduleTree
