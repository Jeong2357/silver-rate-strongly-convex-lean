-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TerminalConnectorBounds
import StrongSilver.TerminalEntryPrice
import StrongSilver.WorkingTwoSidedAttachment

namespace StrongSilver
open Real Filter
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 2600000

theorem eventually_working_terminal_attachment : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P c : ℝ, ∀ h I t : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      2 ≤ c → 1/32 ≤ 1-μ*c → (∀ a ∈ I, 1-μ*a ≠ 0) →
      (∀ a ∈ t, 0 < a → a ≤ A) → ∀ Y : V, Y ≠ 0 →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace (AttachmentSpace V ℂ) PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++((I++[c])++t) ∧
        J.x (Fin.last n) = retainedMap (W := PhaseSpace) (retainedMap (W := ℂ) (quadraticMultiplier μ t • Y)) ∧
        J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (workingGateFraction A) ∧
        (∀ j, |inner ℝ (unitDirection (J.x 0)) (J.family.z j)| ≤ A^(10 : ℝ)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g j)| ≤ A^(10 : ℝ)*‖J.x 0‖) ∧
        Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))/
          ((4*A^(19 : ℝ)*(1200000 : ℝ)^2)*(Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I))^2) ≤
          ‖J.x (Fin.last n)‖^2/‖J.x 0‖^2 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_working_two_sided_attachment]
    with A hA hattach
  intro μ b T P c h I t W hc hqc hcritical ht Y hY
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hb0 : 0 < b := (Real.rpow_pos_of_pos hA0 _).trans_le W.pivot_lower
  have hT : 0 < T := hb0.trans W.b_lt_T
  have hAT := (div_le_iff₀ hT).mp W.cap_ratio
  have hμAT := mul_le_mul_of_nonneg_left hAT W.mu_positive.le
  have hcap : μ*A ≤ 1/2 := by nlinarith only [hμAT,W.curvature]
  obtain ⟨n₁,Q,hQ,hNraw,hend₁,hsteps₁,hzraw,hgraw,hgain⟩ := terminal_connector_bounds W.mu_positive hc hqc
    (κ := 1) (K := 1) zero_lt_one le_rfl (by linarith only [hc]) hcap I t hcritical ht hY
  let M := maxPrefixProduct μ t
  let m := Real.sqrt M
  let V₀ := ‖Y‖
  let F := Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I)
  let R := 1200000*m*V₀*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I)
  have hM : 1 ≤ M := maxPrefixProduct_ge_one μ t
  have hm : 1 ≤ m := Real.one_le_sqrt.mpr hM
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hmSq : m^2 = M := Real.sq_sqrt (zero_le_one.trans hM)
  have hV : 0 < V₀ := norm_pos_iff.mpr hY
  have hS := smallPositiveSum_nonneg μ I
  have hF : 1 ≤ F := by
    have he : 1 ≤ Real.exp (inverseCharge μ I) := Real.one_le_exp_iff.mpr (inverseCharge_nonneg μ I)
    have hh := mul_le_mul he (show 1 ≤ 1+smallPositiveSum μ I by linarith only [hS])
      (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos _).le
    simpa only [one_mul] using hh
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  have hR : 0 < R := by dsimp only [R]; positivity
  have hReq : R = (1200000 : ℝ)*m*V₀*F := by dsimp only [R,F]; ring
  have hN : ‖Q.x 0‖ ≤ R := by simpa only [mul_one,div_one] using hNraw
  let Z := R+M*V₀
  have hZ0 : 0 ≤ Z := add_nonneg hR.le (mul_nonneg (zero_le_one.trans hM) hV.le)
  have hz : ∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ Z := by
    intro j
    simpa only [mul_one,div_one] using hzraw j
  have hg : ∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ R := by
    intro j
    simpa only [mul_one,div_one] using hgraw j
  obtain ⟨e,he0,L,he,J,hsteps,hsource,hend,hNZ,hPos,hGate,hNsq,hrelative,hRatio⟩ :=
    hattach μ b T P h W (AttachmentSpace V ℂ) n₁ Q hQ Z R hZ0 hR.le hz hg
  have hprice : ‖J.x 0‖^2 ≤ (4*A^(19 : ℝ)*(1200000 : ℝ)^2)*m^3*V₀^2*F^2 :=
    terminal_entry_price hm hV hF (by norm_num) (Real.rpow_pos_of_pos hA0 (19 : ℝ)).le (norm_nonneg _)
      (hN.trans_eq hReq)
      (by rw [← hReq,hmSq]) hReq.le hNsq
  have hEndNorm : ‖J.x (Fin.last _)‖ = ‖Q.x (Fin.last n₁)‖ := by
    rw [hend]
    exact retainedIsometry.norm_map _
  have hterminal : m^2*V₀*Real.exp (-2*(μ*Scalar.SignedIntervals.positiveMass t)) ≤ ‖J.x (Fin.last _)‖ := by
    have heq : m^2*V₀*Real.exp (-2*(μ*Scalar.SignedIntervals.positiveMass t)) =
        M*Real.exp (-2*μ*Scalar.SignedIntervals.positiveMass t)*V₀ := by
      rw [hmSq,show -2*(μ*Scalar.SignedIntervals.positiveMass t) = -2*μ*Scalar.SignedIntervals.positiveMass t by ring]
      ring
    rw [heq,hEndNorm]
    exact hgain
  have hresult := terminal_ratio_of_entry_bound hm hV hF0 (by positivity : 0 < 4*A^(19 : ℝ)*(1200000 : ℝ)^2)
    (norm_pos_iff.mpr hNZ) hprice hterminal
  refine ⟨_,J,?_,?_,hNZ,hPos,hGate,hrelative,hresult⟩
  · exact hsteps.trans (congrArg (fun l : List ℝ => (h++[b])++l) hsteps₁)
  · exact hend.trans (congrArg (retainedMap (W := PhaseSpace)) hend₁)

end
end StrongSilver
