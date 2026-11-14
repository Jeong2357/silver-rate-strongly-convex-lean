-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialRaiseScale

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1800000

theorem initial_raised_norm_bound {κ K U s Z H e N : ℝ}
    (hκ : 0 < κ) (hK : 1 ≤ K) (hU : 0 ≤ U) (hs : 0 < s) (hZ : 0 ≤ Z) (hH : 0 ≤ H)
    (hsκ : s*κ ≤ 2*K*U) (he : e^2 = initialRaisedSquare κ s Z H)
    (hN : N^2 ≤ initialSourceNormConstant*K^2*e^2) :
    s^2*N^2 ≤ initialEntryConstant*K^4*(U^2+U*Z+κ*U*H) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hK2 : K ≤ K^2 := by nlinarith only [hK]
  have h2KU : 0 ≤ 2*K*U := by positivity
  have hsκ0 : 0 ≤ s*κ := mul_nonneg hs.le hκ.le
  have hsq := (sq_le_sq₀ hsκ0 h2KU).mpr hsκ
  have hZterm := mul_le_mul_of_nonneg_right hsκ hZ
  have hHterm := mul_le_mul_of_nonneg_right hsκ (mul_nonneg hκ.le hH)
  have hUZ : 0 ≤ U*Z := mul_nonneg hU hZ
  have hκUH : 0 ≤ κ*U*H := mul_nonneg (mul_nonneg hκ.le hU) hH
  have hKZ := mul_le_mul_of_nonneg_right hK2 hUZ
  have hKH := mul_le_mul_of_nonneg_right hK2 hκUH
  have hsum : (s*κ)^2+(s*κ)*Z+(s*κ)*κ*H ≤ 4*K^2*(U^2+U*Z+κ*U*H) := by
    nlinarith only [hsq,hZterm,hHterm,hKZ,hKH,mul_nonneg (sq_nonneg K) hUZ,mul_nonneg (sq_nonneg K) hκUH]
  have hscale := mul_le_mul_of_nonneg_left hN (sq_nonneg s)
  rw [he] at hscale
  have heq : s^2*(initialSourceNormConstant*K^2*initialRaisedSquare κ s Z H) =
      (initialSourceNormConstant*initialRaiseConstant*K^2)*((s*κ)^2+(s*κ)*Z+(s*κ)*κ*H) := by
    unfold initialRaisedSquare
    field_simp [hs.ne'] <;> ring
  rw [heq] at hscale
  have hcoef : 0 ≤ initialSourceNormConstant*initialRaiseConstant*K^2 := by
    have := initialSourceNormConstant_positive
    have := initialRaiseConstant_positive
    positivity
  have hm := mul_le_mul_of_nonneg_left hsum hcoef
  apply hscale.trans (hm.trans_eq ?_)
  unfold initialEntryConstant
  ring

end
end StrongSilver
