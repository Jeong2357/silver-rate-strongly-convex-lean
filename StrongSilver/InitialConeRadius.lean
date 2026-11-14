-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialConeSize
import StrongSilver.ConeLocalTrajectory

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1600000

def initialConeRadiusConstant : ℝ := 4*initialConeConstant

theorem initialConeConstant_dominates : 1 ≤ initialConeConstant ∧
    initialPointRelativeConstant ≤ initialConeConstant ∧ initialSlopeRelativeConstant ≤ initialConeConstant := by
  have hp := initialPointRelativeConstant_positive
  have hg := initialSlopeRelativeConstant_positive
  have hc := initialGateConstant_positive
  have hquot : 0 ≤ 512*initialPointRelativeConstant/initialGateConstant := by positivity
  unfold initialConeConstant
  constructor
  · linarith only [hp,hg,hquot]
  · constructor <;> linarith only [hp,hg,hquot]

theorem initialConeRadiusConstant_positive : 0 < initialConeRadiusConstant := by
  have := initialConeConstant_positive
  unfold initialConeRadiusConstant
  positivity

namespace ConeConnectorParameters
variable {μ b κ K V : ℝ}
    (C : ConeConnectorParameters μ b V (initialPointRelativeConstant*K)
      (initialSlopeRelativeConstant*K*V/κ) (initialGateConstant/K^2))

theorem initial_radius_size (hμ : 0 ≤ μ) (hb : 2 ≤ b) (hbκ : b ≤ κ)
    (hκ : 0 < κ) (hK : 1 ≤ K) (hV : 0 < V) (hκKb : κ ≤ K*b) (hq : 1/32 ≤ 1-μ*b) :
    C.U ≤ initialConeRadiusConstant*K^4*V ∧ κ*(2*C.a) ≤ initialConeRadiusConstant*K^4*V ∧
      initialPointRelativeConstant*K*V ≤ initialConeRadiusConstant*K^4*V ∧
      initialSlopeRelativeConstant*K*V ≤ initialConeRadiusConstant*K^4*V := by
  have hsize := initial_cone_size hμ hb hbκ hκ hK hV hκKb hq C
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hK2 : 1 ≤ K^2 := by nlinarith only [hK]
  have hK23 := mul_le_mul_of_nonneg_right hK2 hK0.le
  have hK3 : K ≤ K^3 := by nlinarith only [hK23]
  have hK34 := mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ K^3)
  have hK14 : K ≤ K^4 := by nlinarith only [hK3,hK34]
  have hCpos := initialConeConstant_positive
  have hdom := initialConeConstant_dominates
  have hUscale := mul_le_mul_of_nonneg_right hK34 (mul_nonneg hCpos.le hV.le)
  have hPoint := mul_le_mul hdom.2.1 hK14 hK0.le hCpos.le
  have hSlope := mul_le_mul hdom.2.2 hK14 hK0.le hCpos.le
  have hPV := mul_le_mul_of_nonneg_right hPoint hV.le
  have hGV := mul_le_mul_of_nonneg_right hSlope hV.le
  have hbase : 0 ≤ initialConeConstant*K^4*V := by positivity
  unfold initialConeRadiusConstant
  exact ⟨by nlinarith only [hsize.1,hUscale,hbase],hsize.2,
    by nlinarith only [hPV,hbase],by nlinarith only [hGV,hbase]⟩

theorem initial_trace_radius (hμ : 0 ≤ μ) (hb : 2 ≤ b) (hbκ : b ≤ κ)
    (hκ : 0 < κ) (hK : 1 ≤ K) (hV : 0 < V) (hκKb : κ ≤ K*b) (hq : 1/32 ≤ 1-μ*b) (I : List ℝ) :
    C.traceRadius I ≤ initialConeRadiusConstant*K^4*V*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ) := by
  have hsize := C.initial_radius_size hμ hb hbκ hκ hK hV hκKb hq
  have hcoef : (1-μ)*(2*C.a) ≤ 2*C.a := by nlinarith only [mul_nonneg hμ C.a_pos.le]
  have hG : 2*C.a ≤ (initialConeRadiusConstant*K^4*V)/κ :=
    (le_div_iff₀ hκ).mpr (by nlinarith only [hsize.2.1])
  have hsum := mul_le_mul_of_nonneg_right (hcoef.trans hG) (smallPositiveSum_nonneg μ I)
  have hbound : C.U+(1-μ)*(2*C.a)*smallPositiveSum μ I ≤
      (initialConeRadiusConstant*K^4*V)*(1+smallPositiveSum μ I/κ) := by
    have he : ((initialConeRadiusConstant*K^4*V)/κ)*smallPositiveSum μ I =
        (initialConeRadiusConstant*K^4*V)*(smallPositiveSum μ I/κ) := by ring
    rw [he] at hsum
    nlinarith only [hsize.1,hsum]
  have hh := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (inverseCharge μ I)).le
  unfold traceRadius
  nlinarith only [hh]

end ConeConnectorParameters
end
end StrongSilver
