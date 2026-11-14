-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TerminalConnectorBounds
import StrongSilver.TerminalEntryPrice
import StrongSilver.InitialTwoSidedAttachment

namespace StrongSilver
open Real Filter
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 2800000

theorem eventually_initial_terminal_attachment : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B c : ℝ, ∀ h I t : List ℝ, InitialPhaseBudget A μ b T κ B h →
      2 ≤ c → B ≤ c → 1/32 ≤ 1-μ*c → μ*B ≤ 1/2 → (∀ a ∈ I, 1-μ*a ≠ 0) →
      (∀ a ∈ t, 0 < a → a ≤ B) → ∀ Y : V, Y ≠ 0 →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace (AttachmentSpace V ℂ) PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++((I++[c])++t) ∧
        J.x (Fin.last n) = retainedMap (W := PhaseSpace) (retainedMap (W := ℂ) (quadraticMultiplier μ t • Y)) ∧
        J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (initialGateConstant/(κ/B)^2) ∧
        (∀ j, |inner ℝ (unitDirection (J.x 0)) (J.family.z j)| ≤ initialPointRelativeConstant*(κ/B)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g j)| ≤ initialSlopeRelativeConstant*(κ/B)*‖J.x 0‖/κ) ∧
        Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))/
          ((4*initialEntryConstant*(1200000 : ℝ)^2*(κ/B)^6)*
            (Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ))^2) ≤
          ‖J.x (Fin.last n)‖^2/‖J.x 0‖^2 := by
  filter_upwards [eventually_initial_two_sided_attachment] with A hattach
  intro μ b T κ B c h I t W hc hcB hqc hcap hcritical ht Y hY
  let K := κ/B
  have hK : 1 ≤ K := W.ratio_ge_one
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hκKc : κ ≤ K*c := by
    have hh := mul_le_mul_of_nonneg_left hcB hK0.le
    have he : K*B = κ := by dsimp only [K]; field_simp [W.B_positive.ne']
    rwa [he] at hh
  obtain ⟨n₁,Q,hQ,hN,hend₁,hsteps₁,hz,hg,hgain⟩ := terminal_connector_bounds W.mu_positive hc hqc
    W.kappa_positive hK hκKc hcap I t hcritical ht hY
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
  have hS := smallPositiveSum_nonneg μ I
  have hF : 1 ≤ F := by
    have he : 1 ≤ Real.exp (inverseCharge μ I) := Real.one_le_exp_iff.mpr (inverseCharge_nonneg μ I)
    have hs : 1 ≤ 1+smallPositiveSum μ I/κ := by have := div_nonneg hS W.kappa_positive.le; linarith
    have hh := mul_le_mul he hs (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos _).le
    simpa only [one_mul] using hh
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  have hκ0 := W.kappa_positive
  have hR : 0 < R := by dsimp only [R]; positivity
  have hReq : R = (1200000*K)*m*V₀*F := by dsimp only [R,F]; ring
  let Z := R+M*V₀
  let H := R/κ
  have hZ0 : 0 ≤ Z := add_nonneg hR.le (mul_nonneg (zero_le_one.trans hM) hV.le)
  have hH0 : 0 ≤ H := div_nonneg hR.le W.kappa_positive.le
  obtain ⟨n₂,J,hsteps,hend,hNZ,hPos,hGate,hNsq,hrelative⟩ := hattach μ b T κ B h W (AttachmentSpace V ℂ) n₁ Q hQ Z H hZ0 hH0 hz hg
  have hEntry : ‖J.x 0‖^2 ≤ (initialEntryConstant*K^4)*(‖Q.x 0‖^2+‖Q.x 0‖*Z+‖Q.x 0‖*(κ*H)) := by
    calc
      _ ≤ initialEntryConstant*K^4*(‖Q.x 0‖^2+‖Q.x 0‖*Z+κ*‖Q.x 0‖*H) := hNsq
      _ = _ := by ring
  have hHbound : κ*H ≤ (1200000*K)*m*V₀*F := by
    dsimp only [H]
    have he : κ*(R/κ) = R := by field_simp [W.kappa_positive.ne']
    rw [he,hReq]
  have hprice₀ := terminal_entry_price hm hV hF (by linarith only [hK] : 1 ≤ 1200000*K)
    (by have := initialEntryConstant_positive; positivity : 0 ≤ initialEntryConstant*K^4) (norm_nonneg _)
    (hN.trans_eq hReq) (by rw [← hReq,hmSq]) hHbound hEntry
  have hprice : ‖J.x 0‖^2 ≤ (4*initialEntryConstant*(1200000 : ℝ)^2*K^6)*m^3*V₀^2*F^2 := by
    apply hprice₀.trans_eq
    ring
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
  have hCoef : 0 < 4*initialEntryConstant*(1200000 : ℝ)^2*K^6 := by
    have := initialEntryConstant_positive
    positivity
  have hresult := terminal_ratio_of_entry_bound hm hV hF0 hCoef (norm_pos_iff.mpr hNZ) hprice hterminal
  refine ⟨n₂,J,?_,?_,hNZ,hPos,hGate,hrelative,hresult⟩
  · exact hsteps.trans (congrArg (fun l : List ℝ => (h++[b])++l) hsteps₁)
  · exact hend.trans (congrArg (retainedMap (W := PhaseSpace)) hend₁)

end
end StrongSilver
