-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.SignedIntervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace StrongSilver
open Real Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2600000

/-- A missing signed-prefix mass produces the logarithmic visibility
charge used to control balanced vertices that fail the good test. -/
theorem visibility_log_deficit {δ t mass deficit K : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (ht : 0 < t) (hm : 0 < mass) (hd : 0 ≤ deficit)
    (hK : 0 < K) (hsize : mass ≤ K*t) (hdeficit : δ*t/2 ≤ deficit) :
    δ/(2*K+1) ≤ Real.log (1+deficit/mass) := by
  have hsum : 0 < mass+deficit := add_pos_of_pos_of_nonneg hm hd
  have harg : 0 < 1+deficit/mass := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos harg
  have hid : 1-(1+deficit/mass)⁻¹ = deficit/(mass+deficit) := by
    field_simp [hm.ne',hsum.ne'] <;> ring
  rw [hid] at hlog
  apply le_trans _ hlog
  have hden : 0 < 2*K+1 := by linarith only [hK]
  apply (div_le_div_iff₀ hden hsum).mpr
  have hsize' := mul_le_mul_of_nonneg_left hsize hδ
  have hdeficit' := mul_le_mul_of_nonneg_left hdeficit hK.le
  have hδdeficit := mul_le_mul_of_nonneg_right hδ1 hd
  nlinarith only [hsize',hdeficit',hδdeficit]

/-- Child deficits remain present in the full visible interval. -/
theorem visible_parent_deficit (L R : List ℝ) (pivot : ℝ) :
    positiveMass L-prefixMax L ≤ positiveMass (L++pivot::R)-prefixMax (L++pivot::R) := by
  simpa only [List.nil_append] using interval_deficit_mono [] L (pivot::R)

end
end StrongSilver
