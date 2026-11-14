-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeSizeBounds
import StrongSilver.InitialConstantBounds

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2400000

def initialConeConstant : ℝ := 512*(1+512*initialPointRelativeConstant/initialGateConstant+
  initialPointRelativeConstant+32*initialSlopeRelativeConstant)

theorem initialConeConstant_positive : 0 < initialConeConstant := by
  have := initialPointRelativeConstant_positive
  have := initialSlopeRelativeConstant_positive
  have := initialGateConstant_positive
  unfold initialConeConstant
  positivity

theorem initial_cone_size {μ b κ K V : ℝ} (hμ : 0 ≤ μ) (hb : 2 ≤ b) (hbκ : b ≤ κ)
    (hκ : 0 < κ) (hK : 1 ≤ K) (hV : 0 < V) (hκKb : κ ≤ K*b) (hq : 1/32 ≤ 1-μ*b)
    (C : ConeConnectorParameters μ b V (initialPointRelativeConstant*K)
      (initialSlopeRelativeConstant*K*V/κ) (initialGateConstant/K^2)) :
    C.U ≤ initialConeConstant*K^3*V ∧ κ*(2*C.a) ≤ 4*initialConeConstant*K^4*V := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hb0 : 0 < b := by linarith only [hb]
  have hq0 : 0 < 1-μ*b := by linarith only [hq]
  have hq1 : 1-μ*b ≤ 1 := by have hh := mul_nonneg hμ hb0.le; linarith only [hh]
  have hc := initialGateConstant_positive
  have hCp := initialPointRelativeConstant_positive
  have hCg := initialSlopeRelativeConstant_positive
  have hη : 0 < initialGateConstant/K^2 := div_pos hc (sq_pos_of_pos hK0)
  have hK2 : 1 ≤ K^2 := by nlinarith only [hK]
  have hη1 : initialGateConstant/K^2 ≤ 1 := (div_le_one (sq_pos_of_pos hK0)).mpr
    (initialGateConstant_le_one.trans hK2)
  have hM : 1 ≤ initialPointRelativeConstant*K := by
    have hh := mul_le_mul initialPointRelativeConstant_ge_one hK (by norm_num : (0 : ℝ) ≤ 1) hCp.le
    simpa only [one_mul] using hh
  have hH : 0 ≤ initialSlopeRelativeConstant*K*V/κ := by positivity
  have hlo : (1/32 : ℝ)*(initialGateConstant/K^2) ≤ (1-μ*b)*(initialGateConstant/K^2) :=
    mul_le_mul_of_nonneg_right hq hη.le
  have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ 16*(initialPointRelativeConstant*K)*V)
    (by positivity : 0 < (1/32 : ℝ)*(initialGateConstant/K^2)) hlo
  have hediv : (16*(initialPointRelativeConstant*K)*V)/((1/32 : ℝ)*(initialGateConstant/K^2)) =
      (512*initialPointRelativeConstant/initialGateConstant)*K^3*V := by
    field_simp [hc.ne',hK0.ne'] <;> ring
  rw [hediv] at hdiv
  have hBH := mul_le_mul_of_nonneg_right hbκ hH
  have heH : κ*(initialSlopeRelativeConstant*K*V/κ) = initialSlopeRelativeConstant*K*V := by
    field_simp [hκ.ne']
  rw [heH] at hBH
  have hdivH := div_le_div_of_nonneg_left (mul_nonneg hb0.le hH) (by norm_num : (0 : ℝ) < 1/32) hq
  have hedivH : (b*(initialSlopeRelativeConstant*K*V/κ))/(1/32 : ℝ) = 32*(b*(initialSlopeRelativeConstant*K*V/κ)) := by ring
  rw [hedivH] at hdivH
  have htermH : (b*(initialSlopeRelativeConstant*K*V/κ))/(1-μ*b) ≤ 32*initialSlopeRelativeConstant*K*V := by
    have hh := mul_le_mul_of_nonneg_left hBH (by norm_num : (0 : ℝ) ≤ 32)
    nlinarith only [hdivH,hh]
  have hK23 := mul_le_mul_of_nonneg_right hK2 hK0.le
  have hK13 : 1 ≤ K^3 := by nlinarith only [hK23,hK]
  have hK3 : K ≤ K^3 := by nlinarith only [hK23]
  have hV3 := mul_le_mul_of_nonneg_right hK13 hV.le
  have hMV3 := mul_le_mul_of_nonneg_right hK3 (mul_nonneg hCp.le hV.le)
  have hHV3 := mul_le_mul_of_nonneg_right hK3 (mul_nonneg hCg.le hV.le)
  have hU := C.U_linear_bound hμ hb0.le hq0 hV.le hM hH hη hη1
  have hUbound : C.U ≤ initialConeConstant*K^3*V := by
    unfold initialConeConstant
    ring_nf at hU hdiv htermH hV3 hMV3 hHV3 ⊢
    linarith only [hU,hdiv,htermH,hV3,hMV3,hHV3]
  have hD : b/2 ≤ (1-μ)*b := by nlinarith only [hq,hb]
  have hDa := mul_le_mul_of_nonneg_right hD C.a_pos.le
  have hqU := mul_le_mul_of_nonneg_right hq1 C.U_pos.le
  have hba : b*C.a ≤ 2*C.U := by nlinarith only [hDa,hqU,C.connector_a]
  have hκa := mul_le_mul_of_nonneg_right hκKb C.a_pos.le
  have hbaK := mul_le_mul_of_nonneg_left hba hK0.le
  have hUscale := mul_le_mul_of_nonneg_left hUbound (by positivity : 0 ≤ 4*K)
  exact ⟨hUbound,by nlinarith only [hκa,hbaK,hUscale]⟩

end
end StrongSilver
