-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FarScaledLogEnvelope
import StrongSilver.PowerLogFloor

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1800000

def farPowerLoss (Cneg Ctail σ τ υ ξ ε a B : ℝ) : ℝ :=
  splitCoefficient*(2*farScaledLogEnvelope Cneg Ctail σ τ υ ξ ε a B+
    (4800/(1-ξ))*(1/Real.log B+ξ))

theorem tendsto_farPowerLoss {σ τ υ ξ ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hσ : nu+(1-ξ)*(-nu*(1+σ)) < 0) (hτ : nu+(1-ξ)*(-nu-τ) < 0)
    (hυ : nu+(1-ξ)*(-nu*(1+υ)) < 0) (Cneg Ctail a : ℝ) :
    Tendsto (farPowerLoss Cneg Ctail σ τ υ ξ ε a) atTop
      (𝓝 (splitCoefficient*((4800/(1-ξ))*ξ))) := by
  have hΦ := tendsto_farScaledLogEnvelope hε hε1 hσ hτ hυ Cneg Ctail a
  have hlog : Tendsto (fun B : ℝ => 1/Real.log B) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hh := ((hΦ.const_mul 2).add ((hlog.add_const ξ).const_mul (4800/(1-ξ)))).const_mul splitCoefficient
  simp only [mul_zero,zero_add,add_zero] at hh
  apply hh.congr'
  exact Filter.Eventually.of_forall (fun B => by rfl)

theorem eventually_farPowerLoss_small {σ τ υ ξ ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hσ : nu+(1-ξ)*(-nu*(1+σ)) < 0) (hτ : nu+(1-ξ)*(-nu-τ) < 0)
    (hυ : nu+(1-ξ)*(-nu*(1+υ)) < 0)
    (hcount : splitCoefficient*((4800/(1-ξ))*ξ) < powerLogMinimum/4) (Cneg Ctail a : ℝ) :
    ∀ᶠ B : ℝ in atTop, farPowerLoss Cneg Ctail σ τ υ ξ ε a B ≤ powerLogMinimum/4 := by
  have hh := (tendsto_order.1 (tendsto_farPowerLoss hε hε1 hσ hτ hυ Cneg Ctail a)).2 _ hcount
  exact hh.mono (fun _ hb => hb.le)

end
end StrongSilver
