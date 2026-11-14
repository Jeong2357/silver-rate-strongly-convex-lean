-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TerminalConnectorBounds
import StrongSilver.TerminalEntryPrice

namespace StrongSilver
open Real
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 2200000

theorem terminal_connector_ratio {μ c A κ K : ℝ} (hμ : 0 < μ) (hc : 2 ≤ c) (hqc : 1/32 ≤ 1-μ*c)
    (hκ : 0 < κ) (hK : 1 ≤ K) (hκKc : κ ≤ K*c) (hcap : μ*A ≤ 1/2)
    (I t : List ℝ) (hcritical : ∀ b ∈ I, 1-μ*b ≠ 0) (ht : ∀ b ∈ t, 0 < b → b ≤ A)
    {Y : V} (hY : Y ≠ 0) :
    ∃ n : ℕ, ∃ Q : SupportedPath (AttachmentSpace V ℂ) μ n, Q.x 0 ≠ 0 ∧
      List.ofFn Q.steps = (I++[c])++t ∧
      Q.x (Fin.last n) = retainedMap (W := ℂ) (quadraticMultiplier μ t • Y) ∧
      Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))/
        ((4*(1200000*K)^2)*(Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ))^2) ≤
        ‖Q.x (Fin.last n)‖^2/‖Q.x 0‖^2 := by
  obtain ⟨n,Q,hQ,hN,hend,hsteps,hz,hg,hgain⟩ := terminal_connector_bounds hμ hc hqc hκ hK hκKc hcap I t hcritical ht hY
  let M := maxPrefixProduct μ t
  let m := Real.sqrt M
  let V₀ := ‖Y‖
  let F := Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ)
  let R := 1200000*K*m*V₀*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ)
  have hM : 1 ≤ M := maxPrefixProduct_ge_one μ t
  have hm : 1 ≤ m := Real.one_le_sqrt.mpr hM
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hmSq : m^2 = M := Real.sq_sqrt (zero_le_one.trans hM)
  have hV : 0 < V₀ := norm_pos_iff.mpr hY
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hS := smallPositiveSum_nonneg μ I
  have hF : 1 ≤ F := by
    have he : 1 ≤ Real.exp (inverseCharge μ I) := Real.one_le_exp_iff.mpr (inverseCharge_nonneg μ I)
    have hs : 1 ≤ 1+smallPositiveSum μ I/κ := by have := div_nonneg hS hκ.le; linarith
    have hh := mul_le_mul he hs (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos _).le
    simpa only [one_mul] using hh
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  have hR : 0 < R := by dsimp only [R]; positivity
  have hReq : R = (1200000*K)*m*V₀*F := by dsimp only [R,F]; ring
  have hprice₀ := terminal_entry_price hm hV hF (by linarith only [hK] : 1 ≤ 1200000*K) zero_le_one (norm_nonneg (Q.x 0))
    (hN.trans_eq hReq)
    (show 0 ≤ (1200000*K)*m*V₀*F+m^2*V₀ by rw [← hReq]; positivity)
    (show 0 ≤ (1200000*K)*m*V₀*F by rw [← hReq]; exact hR.le)
    (show ‖Q.x 0‖^2 ≤ 1*(‖Q.x 0‖^2+‖Q.x 0‖*0+‖Q.x 0‖*0) by
      simpa only [mul_zero,add_zero,one_mul] using (le_refl (‖Q.x 0‖^2)))
  have hprice : ‖Q.x 0‖^2 ≤ (4*(1200000*K)^2)*m^3*V₀^2*F^2 := by simpa only [mul_one] using hprice₀
  have hterminal : m^2*V₀*Real.exp (-2*(μ*Scalar.SignedIntervals.positiveMass t)) ≤ ‖Q.x (Fin.last n)‖ := by
    have heq : m^2*V₀*Real.exp (-2*(μ*Scalar.SignedIntervals.positiveMass t)) =
        M*Real.exp (-2*μ*Scalar.SignedIntervals.positiveMass t)*V₀ := by
      rw [hmSq,show -2*(μ*Scalar.SignedIntervals.positiveMass t) = -2*μ*Scalar.SignedIntervals.positiveMass t by ring]
      ring
    rw [heq]
    exact hgain
  have hresult := terminal_ratio_of_entry_bound hm hV hF0 (by positivity : 0 < 4*(1200000*K)^2)
    (norm_pos_iff.mpr hQ) hprice hterminal
  exact ⟨n,Q,hQ,hsteps,hend,hresult⟩

end
end StrongSilver
