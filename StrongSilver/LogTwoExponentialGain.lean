-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

/-- Quantitative logarithmic estimate for the exact four-phase norm
identity. The hypotheses are scalar bounds, later discharged by the
closed perturbation box. -/
theorem log_two_exponential_gain {g l r c c₀ K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hsmall : K*ε ≤ 1)
    (hc : 0 ≤ c) (hc2 : c ≤ 2)
    (hg : |g| ≤ K*ε) (hv : |g+l+r| ≤ K*ε)
    (hclose : |c-c₀| ≤ K*ε)
    (hN : 0 < Real.exp (-g)+c*(Real.exp (-g-l-r)-1)) :
    g+c₀*(g+l+r)-(4*K)*ε*(|g|+|l|+|r|) ≤
      -Real.log (Real.exp (-g)+c*(Real.exp (-g-l-r)-1)) := by
  let v := g+l+r
  have hv' : |v| ≤ K*ε := hv
  have hKe : 0 ≤ K*ε := mul_nonneg hK hε
  have heG : Real.exp (-g) ≤ 1-g+g^2 := by
    have hh := Real.abs_exp_sub_one_sub_id_le (x := -g) (by simpa only [abs_neg] using hg.trans hsmall)
    have hl := le_abs_self (Real.exp (-g)-1-(-g))
    nlinarith only [hh,hl]
  have heV : Real.exp (-v) ≤ 1-v+v^2 := by
    have hh := Real.abs_exp_sub_one_sub_id_le (x := -v) (by simpa only [abs_neg] using hv'.trans hsmall)
    have hl := le_abs_self (Real.exp (-v)-1-(-v))
    nlinarith only [hh,hl]
  have hG2 : g^2 ≤ K*ε*|g| := by
    have hh := mul_le_mul_of_nonneg_right hg (abs_nonneg g)
    nlinarith only [hh,sq_abs g]
  have hV2 : v^2 ≤ K*ε*|v| := by
    have hh := mul_le_mul_of_nonneg_right hv' (abs_nonneg v)
    nlinarith only [hh,sq_abs v]
  have hd : (c-c₀)*v ≥ -K*ε*|v| := by
    have ha : |(c-c₀)*v| ≤ K*ε*|v| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hclose (abs_nonneg v)
    have hb := neg_abs_le ((c-c₀)*v)
    linarith only [ha,hb]
  have hcV := mul_le_mul_of_nonneg_left heV hc
  have hcv2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg v)
  have hnorm : Real.exp (-g)+c*(Real.exp (-v)-1) ≤
      1-g-c₀*v+K*ε*|g|+3*K*ε*|v| := by
    nlinarith only [heG,hcV,hcv2,hG2,hV2,hd]
  have habs : |v| ≤ |g|+|l|+|r| := (abs_add_le (g+l) r).trans
    (add_le_add (abs_add_le g l) le_rfl)
  have hgs : |g| ≤ |g|+|l|+|r| := by linarith only [abs_nonneg l,abs_nonneg r]
  have hprice : K*ε*|g|+3*K*ε*|v| ≤ 4*K*ε*(|g|+|l|+|r|) := by
    have h1 := mul_le_mul_of_nonneg_left hgs hKe
    have h2 := mul_le_mul_of_nonneg_left habs hKe
    nlinarith only [h1,h2]
  have hvexp : -g-l-r = -v := by dsimp [v]; ring
  rw [hvexp] at hN ⊢
  have hlog := Real.log_le_sub_one_of_pos hN
  dsimp [v] at hnorm hprice hlog ⊢
  linarith only [hnorm,hprice,hlog]

end
end StrongSilver
