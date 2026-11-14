-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerNormalization

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem quadratic_padding_power_bound {A K b M Q J q D : ℝ} (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hb : 1 ≤ b) (hM : 0 ≤ M) (hMQ : M ≤ Q) (hJ0 : 0 ≤ J)
    (hbA : b ≤ A^((201 : ℝ)/200)) (hQ : A^((49 : ℝ)/50) ≤ Q)
    (hJ : J ≤ A^(-(1 : ℝ)/5)*M+K*A^((1 : ℝ)/2))
    (hq : 1/K ≤ q) (hpad : q*D^2 = (b-1)*J) :
    D^2 ≤ 2*K^2*A^(-(7 : ℝ)/40)*Q^2 := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hqK : 1 ≤ q*K := (div_le_iff₀ hK0).mp hq
  have hDq := mul_le_mul_of_nonneg_right hqK (sq_nonneg D)
  have hpadK := congrArg (fun t : ℝ => K*t) hpad
  have hDb : D^2 ≤ K*b*J := by
    have hKJ := mul_nonneg hK0.le hJ0
    nlinarith only [hDq,hpadK,hKJ]
  have hDJ := mul_le_mul_of_nonneg_left hJ (mul_nonneg hK0.le (zero_le_one.trans hb))
  have hf : b*A^(-(1 : ℝ)/5)*M ≤ A^((161 : ℝ)/200)*Q := by
    calc
      _ ≤ A^((201 : ℝ)/200)*A^(-(1 : ℝ)/5)*Q := by gcongr
      _ = _ := by rw [← Real.rpow_add hA0]; congr 1; norm_num
  have hs : b*A^((1 : ℝ)/2) ≤ A^((301 : ℝ)/200) := by
    calc
      _ ≤ A^((201 : ℝ)/200)*A^((1 : ℝ)/2) :=
        mul_le_mul_of_nonneg_right hbA (Real.rpow_pos_of_pos hA0 _).le
      _ = _ := by rw [← Real.rpow_add hA0]; norm_num
  have hfs := power_times_le_scaled_square (r := (161 : ℝ)/200) hA0 hQ
  norm_num at hfs
  have hss := power_le_scaled_square (r := (301 : ℝ)/200) hA0 hQ
  norm_num at hss
  have hexp : A^(-(91 : ℝ)/200) ≤ A^(-(7 : ℝ)/40) :=
    Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hsq := mul_le_mul_of_nonneg_right hexp (sq_nonneg Q)
  norm_num at hsq
  have hfK := mul_le_mul_of_nonneg_left (hf.trans hfs) hK0.le
  have hsK := mul_le_mul_of_nonneg_left (hs.trans (hss.trans hsq)) (sq_nonneg K)
  have hKsq : K ≤ K^2 := by nlinarith only [hK]
  have hKK := mul_le_mul_of_nonneg_right hKsq
    (mul_nonneg (Real.rpow_pos_of_pos hA0 (-(7 : ℝ)/40)).le (sq_nonneg Q))
  norm_num at hDb hDJ hfK hsK hKK ⊢
  nlinarith only [hDb,hDJ,hfK,hsK,hKK]

end
end StrongSilver
