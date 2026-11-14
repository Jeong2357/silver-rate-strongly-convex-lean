-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianBalanceRatios
import StrongSilver.ReservedTreeNodes

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3600000

/-- A balanced actual signed interval has prefix mass comparable to
its own transformed root step. -/
theorem silverBalanced_root_mass {φ : ℝ → ℝ} {ε : ℝ} {t : ScheduleTree}
    (hε : ε ≤ 1/4) (hb : SilverBalanced φ ε t) :
    φ t.rootStep ≤ t.prefixMass φ ∧ t.prefixMass φ ≤ 9*φ t.rootStep := by
  cases t with
  | leaf word => exact False.elim hb
  | split l b r =>
    have hL := abs_le.mp hb.2.1
    have hR := abs_le.mp hb.2.2.1
    have hK := abs_le.mp hb.2.2.2
    have hDen := mul_pos rho_positive hb.1
    have hLlo : (3/4:ℝ)*(rho*φ b) ≤ l.prefixMass φ :=
      (le_div_iff₀ hDen).mp (by linarith only [hL.1,hε])
    have hLhi : l.prefixMass φ ≤ (5/4:ℝ)*(rho*φ b) :=
      (div_le_iff₀ hDen).mp (by linarith only [hL.2,hε])
    have hRlo : (3/4:ℝ)*(rho*φ b) ≤ r.prefixMass φ :=
      (le_div_iff₀ hDen).mp (by linarith only [hR.1,hε])
    have hRhi : r.prefixMass φ ≤ (5/4:ℝ)*(rho*φ b) :=
      (div_le_iff₀ hDen).mp (by linarith only [hR.2,hε])
    have hKlo : (3/4:ℝ)*φ b ≤ adjustedExcess φ l b :=
      (le_div_iff₀ hb.1).mp (by linarith only [hK.1,hε])
    have hKhi : adjustedExcess φ l b ≤ (5/4:ℝ)*φ b :=
      (div_le_iff₀ hb.1).mp (by linarith only [hK.2,hε])
    have hKpos : 0 < adjustedExcess φ l b := by linarith only [hKlo,hb.1]
    have hMass := (positive_excess_mass_identity φ l r b hKpos).1
    have hRhoLow := mul_le_mul_of_nonneg_right rho_bounds.1.le hb.1.le
    have hRhoHigh := mul_le_mul_of_nonneg_right rho_bounds.2.le hb.1.le
    simp only [rootStep_split]
    constructor <;> nlinarith only [hLlo,hLhi,hRlo,hRhi,hKlo,hKhi,hMass,hRhoLow,hRhoHigh,hb.1]

end
end StrongSilver.ScheduleTree
