-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialGateRatio

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1800000

def initialRaiseConstant : ℝ := 4*initialHeightConstant*(1+initialProximalConstant)
def initialEntryConstant : ℝ := 4*initialSourceNormConstant*initialRaiseConstant

theorem initialHeightConstant_ge_one : 1 ≤ initialHeightConstant := by
  have hh : 1 ≤ Real.exp 4 := Real.one_le_exp_iff.mpr (by norm_num)
  unfold initialHeightConstant
  linarith only [hh]

theorem initialRaiseConstant_ge_one : 1 ≤ initialRaiseConstant := by
  have hh := initialHeightConstant_ge_one
  have hp := initialProximalConstant_positive
  have hmul := mul_nonneg (sub_nonneg.mpr hh) hp.le
  unfold initialRaiseConstant
  nlinarith only [hh,hp,hmul]

theorem initialRaiseConstant_positive : 0 < initialRaiseConstant := zero_lt_one.trans_le initialRaiseConstant_ge_one
theorem initialEntryConstant_positive : 0 < initialEntryConstant := by
  have := initialSourceNormConstant_positive
  have := initialRaiseConstant_positive
  unfold initialEntryConstant
  positivity

def initialRaisedSquare (κ s Z H : ℝ) : ℝ := initialRaiseConstant*(κ^2+κ*(Z+κ*H)/s)

theorem initialRaisedSquare_positive {κ s Z H : ℝ} (hκ : 0 < κ) (hs : 0 < s) (hZ : 0 ≤ Z) (hH : 0 ≤ H) :
    0 < initialRaisedSquare κ s Z H := by
  unfold initialRaisedSquare
  exact mul_pos initialRaiseConstant_positive (add_pos_of_pos_of_nonneg (sq_pos_of_pos hκ)
    (div_nonneg (mul_nonneg hκ.le (add_nonneg hZ (mul_nonneg hκ.le hH))) hs.le))

theorem initialRaisedSquare_ge_square {κ s Z H : ℝ} (hκ : 0 < κ) (hs : 0 < s) (hZ : 0 ≤ Z) (hH : 0 ≤ H) :
    κ^2 ≤ initialRaisedSquare κ s Z H := by
  have hterm : 0 ≤ κ*(Z+κ*H)/s := div_nonneg (mul_nonneg hκ.le (add_nonneg hZ (mul_nonneg hκ.le hH))) hs.le
  have hh := mul_le_mul_of_nonneg_right initialRaiseConstant_ge_one (sq_nonneg κ)
  have hterm' := mul_nonneg initialRaiseConstant_positive.le hterm
  unfold initialRaisedSquare
  nlinarith only [hh,hterm']

theorem initial_raised_height_cost {κ s Z H e Ja : ℝ} (hκ : 0 < κ) (hs : 0 < s)
    (hZ : 0 ≤ Z) (hH : 0 ≤ H) (he0 : 0 < e) (he : e^2 = initialRaisedSquare κ s Z H)
    (hheight : e^2/(initialHeightConstant*κ) ≤ Ja) :
    κ ≤ e ∧ 2*(2*Z/s+(initialProximalConstant*κ)*H/s) ≤ Ja := by
  have hsq := initialRaisedSquare_ge_square hκ hs hZ hH
  rw [← he] at hsq
  have heκ : κ ≤ e := (sq_le_sq₀ hκ.le he0.le).mp hsq
  have hz : 0 ≤ Z/s := div_nonneg hZ hs.le
  have hh : 0 ≤ κ*H/s := div_nonneg (mul_nonneg hκ.le hH) hs.le
  have hCz := initialProximalConstant_positive
  have hCzZ := mul_nonneg hCz.le hz
  have hCzH := mul_nonneg hCz.le hh
  have heq : e^2/(initialHeightConstant*κ) =
      4*(1+initialProximalConstant)*(κ+Z/s+κ*H/s) := by
    rw [he]
    unfold initialRaisedSquare initialRaiseConstant
    field_simp [initialHeightConstant_positive.ne',hκ.ne',hs.ne'] <;> ring
  rw [heq] at hheight
  refine ⟨heκ,?_⟩
  have hCzκ := mul_nonneg hCz.le hκ.le
  ring_nf at hheight hz hh hCzZ hCzH hCzκ ⊢
  linarith only [hheight,hκ,hz,hh,hCzZ,hCzH,hCzκ]

end
end StrongSilver
