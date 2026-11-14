-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.RaisedPhasePadding
import StrongSilver.WorkingEndpointCap
import StrongSilver.OrdinaryPhaseConstruction
import StrongSilver.TwoSidedPhaseAttachment

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2200000

/-- An explicit increased scalar height discharges both two-sided attachment
costs in a working band. No geometric existence or gate hypothesis is used. -/
theorem eventually_exists_raised_working_phase : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P U Z H : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      0 < U → 0 ≤ Z → 0 ≤ H →
      ∃ e : ℝ, 0 < e ∧ ∃ L : LocalPhaseCertificate A μ b T e h,
        e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+raisedPhasePadding A (U/‖L.path.x (Fin.last _)‖) Z H) ∧
        let s := U/‖L.path.x (Fin.last _)‖
        ∃ d : ℝ, 0 ≤ d ∧ d ≤ ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2 ∧
          workingGateFraction A*L.sourceSlopeCap ≤ d ∧
          s*(planarRadius A 0)*Z ≤ s^2*d ∧
          s*(L.endpointProximalCap (A^(3 : ℝ)))*H ≤
            s^2*(((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2-d) ∧
          (∀ j : ℕ, j ≤ h.length → ‖iterate (h.take j) L.planar.physical L.R‖ ≤ A^(3 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_exists_ordinary_phase,
    eventually_working_planar_all_power,eventually_working_endpoint_cap,
    eventually_working_new_gate_double,eventually_raised_phase_height_cost]
    with A hA hex hplanar hcap hgate hcost
  intro μ b T P U Z H h W hU hZ hH
  obtain ⟨e₀,he₀,L₀,heq₀,hgate₀,hnew₀,hratio₀⟩ := hex μ b T P h W
  let s := U/‖L₀.path.x (Fin.last _)‖
  have hs : 0 < s := div_pos hU (norm_pos_iff.mpr L₀.endpoint_ne_zero)
  let P' := raisedPhasePadding A s Z H
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hP' : 0 < P' := raisedPhasePadding_positive hA0 hs hZ hH
  have hP'lower : A^((49 : ℝ)/50) ≤ P' := raisedPhasePadding_lower hA hs hZ hH
  obtain ⟨e,he0,he⟩ := L₀.working_scalar_scale_exists hP'
  let L := L₀.withScalarScale e he0
  have hEsame : ‖L.path.x (Fin.last _)‖ = ‖L₀.path.x (Fin.last _)‖ :=
    congrArg norm (L₀.withScalarScale_endpoint e he0)
  have hsL : U/‖L.path.x (Fin.last _)‖ = s := by rw [hEsame]
  have heL : e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P') := he
  let Ja := ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2
  let G₀ := L.sourceSlopeCap
  let K := planarRadius A 0
  let C := L.endpointProximalCap (A^(3 : ℝ))
  let η := workingGateFraction A
  have hη : 0 ≤ η := (Real.rpow_pos_of_pos hA0 _).le
  have hG₀ : 0 < G₀ := L.sourceSlopeCap_positive
  have hdouble : 2*η*G₀ ≤ Ja := hgate μ b T e h L P' hP'lower W.cap_ratio W.curvature
    W.mass_time W.mass_pivot W.time_bound W.pivot_lower heL W.negative_charge
  have hr0 : K ≤ 2 := by dsimp [K]; linarith [L.planar.head_radius_bound,L.planar.scale_le]
  have hC : C ≤ A^(5 : ℝ) := hcap μ b T e h L W.cap_ratio W.curvature W.mass_time W.mass_bound W.negative_charge
  have hheight := working_scalar_height_lower hA0 L.T_positive W.curvature W.negative_charge heL
  have hcostJa : 2*(K*Z/s+C*H/s) ≤ Ja :=
    hcost s Z H K C ‖L.R‖ Ja hs hZ hH hr0 hC (norm_nonneg _) hheight
  have hK : 0 ≤ K := (L.planar.radius_pos 0).le
  have hC0 : 0 ≤ C := by
    unfold C LocalPhaseCertificate.endpointProximalCap
    exact div_nonneg (mul_nonneg (by linarith [L.b_large])
      (add_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_pos_of_pos hA0 _).le)
        (mul_nonneg L.terminalInner_nonnegative (Real.exp_pos _).le))) (norm_nonneg _)
  have hCZ : 0 ≤ K*Z/s := div_nonneg (mul_nonneg hK hZ) hs.le
  have hCH : 0 ≤ C*H/s := div_nonneg (mul_nonneg hC0 hH) hs.le
  let d := K*Z/s+η*G₀
  have hd : 0 ≤ d := add_nonneg hCZ (mul_nonneg hη hG₀.le)
  have hdη : η*G₀ ≤ d := le_add_of_nonneg_left hCZ
  have hsum : d+C*H/s ≤ Ja := by dsimp only [d]; nlinarith only [hcostJa,hdouble]
  have hdJa : d ≤ Ja := by linarith only [hsum,hCH]
  have hz : s*K*Z ≤ s^2*d := by
    have hh := mul_le_mul_of_nonneg_left (show K*Z/s ≤ d by dsimp only [d]; linarith [mul_nonneg hη hG₀.le]) (sq_nonneg s)
    have heq : s^2*(K*Z/s) = s*K*Z := by field_simp [hs.ne'] <;> ring
    rwa [heq] at hh
  have hg : s*C*H ≤ s^2*(Ja-d) := by
    have hh := mul_le_mul_of_nonneg_left (show C*H/s ≤ Ja-d by linarith only [hsum]) (sq_nonneg s)
    have heq : s^2*(C*H/s) = s*C*H := by field_simp [hs.ne'] <;> ring
    rwa [heq] at hh
  refine ⟨e,he0,L,?_,?_⟩
  · rw [hsL]
    exact heL
  · dsimp only
    rw [hsL]
    exact ⟨d,hd,hdJa,hdη,hz,hg,fun j hj => hplanar μ b T e h L W.cap_ratio W.curvature W.mass_time W.mass_bound j⟩

end
end StrongSilver
