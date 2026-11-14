-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialAssemblyLog
import StrongSilver.LogOnePlusBudget

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1800000

def initialLogPriceConstant : ℝ :=
  16+|Real.log initialEntryConstant|+2*|Real.log initialBlockConstant|+
    |Real.log (4*initialEntryConstant*(1200000 : ℝ)^2)|+|Real.log (2*initialEntryConstant)|+
    |Real.log (4*(1200000 : ℝ)^2)|

theorem initialLogPriceConstant_bounds : 16 ≤ initialLogPriceConstant ∧
    Real.log initialEntryConstant+2*Real.log initialBlockConstant ≤ initialLogPriceConstant ∧
    Real.log (4*initialEntryConstant*(1200000 : ℝ)^2) ≤ initialLogPriceConstant ∧
    Real.log (2*initialEntryConstant) ≤ initialLogPriceConstant ∧
    Real.log (4*(1200000 : ℝ)^2) ≤ initialLogPriceConstant := by
  have ha := abs_nonneg (Real.log initialEntryConstant)
  have hb := abs_nonneg (Real.log initialBlockConstant)
  have hc := abs_nonneg (Real.log (4*initialEntryConstant*(1200000 : ℝ)^2))
  have hd := abs_nonneg (Real.log (2*initialEntryConstant))
  have he := abs_nonneg (Real.log (4*(1200000 : ℝ)^2))
  have hla := le_abs_self (Real.log initialEntryConstant)
  have hlb := le_abs_self (Real.log initialBlockConstant)
  have hlc := le_abs_self (Real.log (4*initialEntryConstant*(1200000 : ℝ)^2))
  have hld := le_abs_self (Real.log (2*initialEntryConstant))
  have hle := le_abs_self (Real.log (4*(1200000 : ℝ)^2))
  unfold initialLogPriceConstant
  constructor
  · linarith only [ha,hb,hc,hd,he]
  constructor
  · linarith only [hla,hlb,hc,hd,he]
  constructor
  · linarith only [ha,hb,hlc,hd,he]
  constructor
  · linarith only [ha,hb,hc,hld,he]
  · linarith only [ha,hb,hc,hd,hle]

theorem initialLogPriceConstant_positive : 0 < initialLogPriceConstant :=
  lt_of_lt_of_le (by norm_num) initialLogPriceConstant_bounds.1

theorem initial_log_price_bounds {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (hK : 1 ≤ κ/B)
    (μ : ℝ) (I t : List ℝ) :
    initialReservedLogPrice κ B μ I ≤ initialLogPriceConstant*(1+Real.log (κ/B))+
      2*inverseCharge μ I+2*Real.log (1+smallPositiveSum μ I/κ) ∧
    initialTerminalLogPrice κ B μ I t ≤ 4*μ*Scalar.SignedIntervals.positiveMass t+
      initialLogPriceConstant*(1+Real.log (κ/B))+2*inverseCharge μ I+2*Real.log (1+smallPositiveSum μ I/κ) ∧
    initialNoConnectorLogPrice κ B μ I t ≤ 4*μ*Scalar.SignedIntervals.positiveMass t+
      initialLogPriceConstant*(1+Real.log (κ/B))+2*inverseCharge μ I+2*Real.log (1+smallPositiveSum μ I/κ) := by
  have hlog := Real.log_nonneg hK
  have hb := initialLogPriceConstant_bounds
  have hprod := mul_nonneg (sub_nonneg.mpr hb.1) hlog
  have hg := log_one_add_nonnegative (div_nonneg (smallPositiveSum_nonneg μ I) hκ.le)
  unfold initialReservedLogPrice initialTerminalLogPrice initialNoConnectorLogPrice
  norm_num at hb ⊢
  constructor
  · nlinarith only [hb.2.1,hprod]
  constructor
  · nlinarith only [hb.2.2.1,hprod,hlog]
  · nlinarith only [hb.2.2.2.1,hprod,hlog,hg]

end
end StrongSilver
