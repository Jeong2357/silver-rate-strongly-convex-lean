-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLastRelativeError
import StrongSilver.FourPhaseMassLogPairBound

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2400000

def signedThreeGain (g l r : ℝ) : ℝ := g+(g+l+r)/Real.sqrt 2

theorem three_gain_error {g l r G L R e : ℝ}
    (he : |g-G|+|l-L|+|r-R| ≤ e) :
    |signedThreeGain g l r-signedThreeGain G L R| ≤ 2*e := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := le_of_lt sqrt_two_bounds.1
  have hsum := (abs_add_le ((g-G)+(l-L)) (r-R)).trans
    (add_le_add (abs_add_le (g-G) (l-L)) le_rfl)
  have hg : |g-G| ≤ e := by linarith only [he,abs_nonneg (l-L),abs_nonneg (r-R)]
  have hv : |(g-G)+(l-L)+(r-R)| ≤ e := hsum.trans he
  have he0 : 0 ≤ e := (by positivity : 0 ≤ |g-G|+|l-L|+|r-R|).trans he
  have hfrac : |((g-G)+(l-L)+(r-R))/Real.sqrt 2| ≤ e := by
    rw [abs_div,abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    nlinarith only [hv,mul_le_mul_of_nonneg_left hs1 he0]
  have hid : signedThreeGain g l r-signedThreeGain G L R =
      (g-G)+((g-G)+(l-L)+(r-R))/Real.sqrt 2 := by unfold signedThreeGain; ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith only [hg,hfrac])

theorem three_abs_error {g l r G L R e : ℝ}
    (he : |g-G|+|l-L|+|r-R| ≤ e) : |g|+|l|+|r| ≤ |G|+|L|+|R|+e := by
  have hg : |g| ≤ |g-G|+|G| := by simpa only [sub_add_cancel] using abs_add_le (g-G) G
  have hl : |l| ≤ |l-L|+|L| := by simpa only [sub_add_cancel] using abs_add_le (l-L) L
  have hr : |r| ≤ |r-R|+|R| := by simpa only [sub_add_cancel] using abs_add_le (r-R) R
  linarith only [he,hg,hl,hr]

/-- Transfer the quantitative geometric lower estimate to the exact
three Cartesian tree gains. Its additional loss is the gain comparison
error, not the larger balance tolerance. -/
theorem three_gain_lower_transfer {g l r G L R C ε e j z : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (he : |g-G|+|l-L|+|r-R| ≤ e)
    (h : signedThreeGain g l r-C*ε*(|g|+|l|+|r|)-j ≤ z) :
    signedThreeGain G L R-C*ε*(|G|+|L|+|R|)-(C+2)*e-j ≤ z := by
  have hf := (abs_le.mp (three_gain_error he)).1
  have ha := three_abs_error he
  have he0 : 0 ≤ e := (by positivity : 0 ≤ |g-G|+|l-L|+|r-R|).trans he
  have hp := mul_le_mul_of_nonneg_left ha (mul_nonneg hC hε)
  have hεe := mul_le_mul_of_nonneg_left hε1 (mul_nonneg hC he0)
  nlinarith only [h,hf,hp,hεe]

/-- Exact change of the normalization in a squared source norm ratio.
This separates the two finite errors in the exterior and total masses. -/
theorem log_normalization_identity {r M m k T K : ℝ}
    (hr : 0 < r) (hM : 0 < M) (hm : 0 < m) (hk : 0 < k) (hT : 0 < T) (hK : 0 < K) :
    Real.log (r*((T*m)/K)^2) = Real.log (r*(M/k)^2)+
      2*Real.log (T*k/K)-2*(Real.log M-Real.log m) := by
  rw [Real.log_mul hr.ne' (pow_pos (div_pos (mul_pos hT hm) hK) 2).ne',
    Real.log_mul hr.ne' (pow_pos (div_pos hM hk) 2).ne',Real.log_pow,Real.log_pow,
    Real.log_div (mul_pos hT hm).ne' hK.ne',Real.log_div hM.ne' hk.ne',
    Real.log_div (mul_pos hT hk).ne' hK.ne',Real.log_mul hT.ne' hm.ne',Real.log_mul hT.ne' hk.ne']
  ring

theorem log_normalization_error {r M m k T K e₁ e₂ : ℝ}
    (hr : 0 < r) (hM : 0 < M) (hm : 0 < m) (hk : 0 < k) (hT : 0 < T) (hK : 0 < K)
    (h₁ : |Real.log (T*k/K)| ≤ e₁) (h₂ : |Real.log M-Real.log m| ≤ e₂) :
    Real.log (r*(M/k)^2)-2*(e₁+e₂) ≤ Real.log (r*((T*m)/K)^2) := by
  rw [log_normalization_identity hr hM hm hk hT hK]
  have h1 := (abs_le.mp h₁).1
  have h2 := (abs_le.mp h₂).2
  linarith only [h1,h2]

end
end StrongSilver.FourPhase
