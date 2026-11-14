-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseNormGain
import StrongSilver.LogTwoExponentialGain

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2600000

variable {x : Shape} (R : Regular x)
include R

theorem log_normPrefactor_upper (hz : 0 ≤ x 7) (hm : 1/2 ≤ x 3) (hM : 1 ≤ totalMass x) :
    Real.log (normPrefactor x) ≤ 3*x 7 := by
  have hz3 := div_nonneg hz R.m3_positive.le
  have hzM := div_nonneg hz R.totalMass_positive.le
  have h3p : 0 < 1+x 7/x 3 := by linarith only [hz3]
  have hMp : 0 < 1+x 7/totalMass x := by linarith only [hzM]
  have hd3 : x 7/x 3 ≤ 2*x 7 := (div_le_iff₀ R.m3_positive).mpr (by nlinarith only [mul_nonneg hz (sub_nonneg.mpr hm)])
  have hdM : x 7/totalMass x ≤ x 7 := (div_le_iff₀ R.totalMass_positive).mpr (by nlinarith only [mul_nonneg hz (sub_nonneg.mpr hM)])
  have hl3 := Real.log_le_sub_one_of_pos h3p
  have hlM := Real.log_le_sub_one_of_pos hMp
  rw [normPrefactor,Real.log_mul h3p.ne' hMp.ne']
  linarith only [hl3,hlM,hd3,hdM]

theorem log_normalizedNorm_identity :
    Real.log (totalMass x^2/‖source x‖^2) =
      -Real.log (normalizedNorm x)-Real.log (normPrefactor x) := by
  have hs : ‖source x‖^2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr (source_nonzero R))).ne'
  have hM : totalMass x^2 ≠ 0 := pow_ne_zero _ R.totalMass_positive.ne'
  have hP : normPrefactor x ≠ 0 := (normPrefactor_positive R).ne'
  rw [normalizedNorm,Real.log_div hM hs,Real.log_div hs (mul_ne_zero hM hP),Real.log_mul hM hP]
  ring

theorem log_norm_gain_lower {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hsmall : K*ε ≤ 1)
    (hc2 : gainCoefficient x ≤ 2)
    (hg : |gain x| ≤ K*ε) (hv : |gain x+gainLeft x+gainRight x| ≤ K*ε)
    (hclose : |gainCoefficient x-1/Real.sqrt 2| ≤ K*ε)
    (hz : 0 ≤ x 7) (hm : 1/2 ≤ x 3) (hM : 1 ≤ totalMass x) :
    gain x+(gain x+gainLeft x+gainRight x)/Real.sqrt 2-
      (4*K)*ε*(|gain x|+|gainLeft x|+|gainRight x|)-3*x 7 ≤
        Real.log (totalMass x^2/‖source x‖^2) := by
  have hc : 0 ≤ gainCoefficient x :=
    (div_pos (mul_pos R.leftMass_positive R.t2_positive) (mul_pos R.k1_positive R.totalTime_positive)).le
  have hN : 0 < Real.exp (-gain x)+gainCoefficient x*(Real.exp (-gain x-gainLeft x-gainRight x)-1) := by
    rw [← normalizedNorm_gain_identity R]
    exact normalizedNorm_positive R
  have hmain := log_two_exponential_gain hK hε hsmall hc hc2 hg hv hclose hN
  rw [← normalizedNorm_gain_identity R] at hmain
  have hprice := log_normPrefactor_upper R hz hm hM
  rw [log_normalizedNorm_identity R]
  simp only [div_eq_mul_inv] at hmain ⊢
  nlinarith only [hmain,hprice]

end
end StrongSilver.FourPhase
