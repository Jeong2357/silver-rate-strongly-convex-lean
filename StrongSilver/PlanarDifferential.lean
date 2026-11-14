-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace StrongSilver
noncomputable section

def planarRiccati (μ r k k' J : ℝ) : ℝ :=
  -r-J/k-μ*((1+k^2)/k*J+(1+k^2+k')/(r*k^2)*J^2)

def planarDerivativeRadial (r k k' J J' : ℝ) : ℝ :=
  -k*r+(J'*k-J*k')/k^2-J

def planarDerivativeTransverse (r k J J' : ℝ) : ℝ := r+J/k+J'

/-- The Riccati equation in Lemma 3.3 is exactly the tangency equation. -/
theorem planar_tangency_identity {μ r k k' J : ℝ} (hr : r ≠ 0) (hk : k ≠ 0) :
    (r+μ*J/k)*planarDerivativeTransverse r k J (planarRiccati μ r k k' J)-
      (μ*J)*planarDerivativeRadial r k k' J (planarRiccati μ r k k' J) = 0 := by
  unfold planarDerivativeTransverse planarDerivativeRadial planarRiccati
  field_simp
  <;> ring

theorem planarRiccati_le {μ r k k' J : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r) (hk : 0 < k)
    (hk' : -1 < k') (hJ : 0 ≤ J) : planarRiccati μ r k k' J ≤ -r-J/k := by
  have hcoef : 0 ≤ 1+k^2+k' := by nlinarith only [sq_nonneg k,hk']
  have hnonneg : 0 ≤ μ*((1+k^2)/k*J+(1+k^2+k')/(r*k^2)*J^2) := by positivity
  unfold planarRiccati
  linarith

/-- The radial component of the boundary derivative is strictly negative. -/
theorem planarDerivativeRadial_neg {r k k' J J' : ℝ} (hr : 0 < r) (hk : 0 < k)
    (hk' : -1 < k') (hJ : 0 ≤ J) (hJ' : J' ≤ -r-J/k) :
    planarDerivativeRadial r k k' J J' < 0 := by
  have hsq : 0 < k^2 := sq_pos_of_pos hk
  have hmul := mul_le_mul_of_nonneg_right hJ' hk.le
  have hdiv : (J/k)*k = J := div_mul_cancel₀ J hk.ne'
  have hJk : 0 ≤ J*(1+k') := mul_nonneg hJ (by linarith)
  have hnum : J'*k-J*k' < 0 := by nlinarith only [hmul,hdiv,hJk,mul_pos hr hk]
  have hratio : (J'*k-J*k')/k^2 < 0 := div_neg_of_neg_of_pos hnum hsq
  unfold planarDerivativeRadial
  nlinarith only [hratio,mul_pos hr hk,hJ]

theorem planar_field_radial_pos {μ r k J : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r) (hk : 0 < k)
    (hJ : 0 ≤ J) : 0 < r+μ*J/k := add_pos_of_pos_of_nonneg hr (by positivity)

theorem planar_boundary_negative_multiple {μ r k k' J : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hk : 0 < k) (hk' : -1 < k') (hJ : 0 ≤ J) :
    ∃ t : ℝ, t < 0 ∧
      planarDerivativeRadial r k k' J (planarRiccati μ r k k' J) = t*(r+μ*J/k) ∧
      planarDerivativeTransverse r k J (planarRiccati μ r k k' J) = t*(μ*J) := by
  let A := r+μ*J/k
  let X := planarDerivativeRadial r k k' J (planarRiccati μ r k k' J)
  let Y := planarDerivativeTransverse r k J (planarRiccati μ r k k' J)
  have hA : 0 < A := planar_field_radial_pos hμ hr hk hJ
  have hX : X < 0 := planarDerivativeRadial_neg hr hk hk' hJ (planarRiccati_le hμ hr hk hk' hJ)
  have hdet : A*Y-(μ*J)*X = 0 := planar_tangency_identity hr.ne' hk.ne'
  refine ⟨X/A,div_neg_of_neg_of_pos hX hA,(div_mul_cancel₀ X hA.ne').symm,?_⟩
  change Y = (X/A)*(μ*J)
  calc
    Y = (X*(μ*J))/A := (eq_div_iff hA.ne').mpr (by nlinarith only [hdet])
    _ = _ := by ring

end
end StrongSilver
