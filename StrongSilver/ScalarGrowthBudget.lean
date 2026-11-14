-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarConstruction

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem scalarRampGrowth_budget_bound {A T b K : ℝ} (hT : 0 < T) (hb : 0 < b) (hK : 1 ≤ K)
    (hAT : A/T ≤ 1/2) (h : List ℝ) (hST : Scalar.SignedIntervals.positiveMass h/T ≤ 2)
    (hSb : Scalar.SignedIntervals.positiveMass h/b ≤ K) :
    scalarRampGrowth T A b h ≤ (2*Real.exp 4)*K := by
  have hden : 0 < T*(1-A/T) := mul_pos hT (by linarith only [hAT])
  have hS := (div_le_iff₀ hT).mp hST
  have hhalf := (div_le_iff₀ hT).mp hAT
  have hratio : Scalar.SignedIntervals.positiveMass h/(T*(1-A/T)) ≤ 4 := by
    apply (div_le_iff₀ hden).mpr
    have he : T*(1-A/T) = T-A := by field_simp [hT.ne'] <;> ring
    rw [he]
    linarith only [hS,hhalf]
  have hexp := Real.exp_le_exp.mpr hratio
  have hfactor : 1+Scalar.SignedIntervals.positiveMass h/b ≤ 2*K := by linarith only [hSb,hK]
  have hfactor0 : 0 ≤ 1+Scalar.SignedIntervals.positiveMass h/b :=
    add_nonneg zero_le_one (div_nonneg (Scalar.SignedIntervals.positiveMass_nonneg h) hb.le)
  have hm := mul_le_mul hexp hfactor hfactor0 (Real.exp_pos 4).le
  unfold scalarRampGrowth
  nlinarith only [hm]

end
end StrongSilver
