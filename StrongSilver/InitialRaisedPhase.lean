-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialRaisedNorm
import StrongSilver.PhaseScalarScale

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2400000

theorem exists_initial_raised_phase {A μ b T κ B e₀ : ℝ} {h : List ℝ}
    (W : InitialPhaseBudget A μ b T κ B h) (L₀ : LocalPhaseCertificate A μ b T e₀ h)
    {U Z H : ℝ} (hU : 0 < U) (hZ : 0 ≤ Z) (hH : 0 ≤ H) :
    ∃ e : ℝ, 0 < e ∧ ∃ L : LocalPhaseCertificate A μ b T e h, κ ≤ e ∧
      e^2 = initialRaisedSquare κ (U/‖L.path.x (Fin.last _)‖) Z H ∧
      let s := U/‖L.path.x (Fin.last _)‖
      ∃ d : ℝ, 0 ≤ d ∧ d ≤ ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2 ∧
        initialGateConstant/(κ/B)^2 ≤ d/L.sourceSlopeCap ∧
        s*(planarRadius A 0)*Z ≤ s^2*d ∧
        s*(L.endpointProximalCap (initialPlaneConstant*κ))*H ≤
          s^2*(((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2-d) ∧
        s^2*‖L.path.x 0‖^2 ≤ initialEntryConstant*(κ/B)^4*(U^2+U*Z+κ*U*H) := by
  let s := U/‖L₀.path.x (Fin.last _)‖
  have hs : 0 < s := div_pos hU (norm_pos_iff.mpr L₀.endpoint_ne_zero)
  have hSq : 0 < initialRaisedSquare κ s Z H := initialRaisedSquare_positive W.kappa_positive hs hZ hH
  let e := Real.sqrt (initialRaisedSquare κ s Z H)
  have he0 : 0 < e := Real.sqrt_pos.mpr hSq
  have he : e^2 = initialRaisedSquare κ s Z H := Real.sq_sqrt hSq.le
  let L := L₀.withScalarScale e he0
  have hEsame : ‖L.path.x (Fin.last _)‖ = ‖L₀.path.x (Fin.last _)‖ :=
    congrArg norm (L₀.withScalarScale_endpoint e he0)
  have hsL : U/‖L.path.x (Fin.last _)‖ = s := by rw [hEsame]
  let Ja := ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2
  obtain ⟨heκ,hcost⟩ := initial_raised_height_cost W.kappa_positive hs hZ hH he0 he (W.height_floor_lower L)
  change 2*(2*Z/s+(initialProximalConstant*κ)*H/s) ≤ Ja at hcost
  have hJa : 0 < Ja := (div_pos (sq_pos_of_pos he0) (mul_pos initialHeightConstant_positive W.kappa_positive)).trans_le
    (W.height_floor_lower L)
  let d := Ja/2
  have hd : 0 ≤ d := div_nonneg hJa.le (by norm_num)
  have hdJa : d ≤ Ja := by dsimp only [d]; linarith only [hJa]
  have hFrac : initialGateConstant/(κ/B)^2 ≤ d/L.sourceSlopeCap := W.gate_fraction_lower L heκ
  have hCz := W.proximal_cap L
  have hCz0 : 0 ≤ (initialProximalConstant*κ)*H/s :=
    div_nonneg (mul_nonneg (mul_nonneg initialProximalConstant_positive.le W.kappa_positive.le) hH) hs.le
  have hZ0 : 0 ≤ 2*Z/s := div_nonneg (mul_nonneg (by norm_num) hZ) hs.le
  have hZcost : 2*Z/s ≤ d := by dsimp only [d]; linarith only [hcost,hCz0]
  have hGcost : (initialProximalConstant*κ)*H/s ≤ Ja-d := by dsimp only [d]; linarith only [hcost,hZ0]
  have hr0 : planarRadius A 0 ≤ 2 := by linarith [L.planar.head_radius_bound,L.planar.scale_le]
  have hz : s*(planarRadius A 0)*Z ≤ s^2*d := by
    have hh := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hr0 hZ) hs.le).trans hZcost
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg s)
    have heq : s^2*((planarRadius A 0)*Z/s) = s*(planarRadius A 0)*Z := by field_simp [hs.ne'] <;> ring
    rwa [heq] at hh'
  have hg : s*(L.endpointProximalCap (initialPlaneConstant*κ))*H ≤ s^2*(Ja-d) := by
    have hh := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCz hH) hs.le).trans hGcost
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg s)
    have heq : s^2*((L.endpointProximalCap (initialPlaneConstant*κ))*H/s) =
        s*(L.endpointProximalCap (initialPlaneConstant*κ))*H := by field_simp [hs.ne'] <;> ring
    rwa [heq] at hh'
  have hElower : B/2 ≤ ‖L₀.path.x (Fin.last _)‖ := by
    linarith [L₀.endpoint_norm_lower,L₀.b_large,W.pivot_lower]
  have hsκ : s*κ ≤ 2*(κ/B)*U := by
    have hdiv := div_le_div_of_nonneg_left hU.le (div_pos W.B_positive (by norm_num : (0 : ℝ) < 2)) hElower
    have hh := mul_le_mul_of_nonneg_right hdiv W.kappa_positive.le
    have heq : (U/(B/2))*κ = 2*(κ/B)*U := by field_simp [W.B_positive.ne'] <;> ring
    rwa [heq] at hh
  have hN := initial_raised_norm_bound W.kappa_positive W.ratio_ge_one hU.le hs hZ hH hsκ he
    (W.source_norm_squared L heκ)
  refine ⟨e,he0,L,heκ,?_,?_⟩
  · rw [hsL]
    exact he
  · dsimp only
    rw [hsL]
    exact ⟨d,hd,hdJa,hFrac,hz,hg,hN⟩

end
end StrongSilver
