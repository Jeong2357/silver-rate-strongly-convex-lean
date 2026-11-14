-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialExceptionalNorm
import StrongSilver.InitialTwoSidedAttachment
import StrongSilver.TwoConeAttachment

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2800000

/-- Traverse a noncritical exceptional gap at the initial cutoff, connect
to a retained suffix, and attach the left initial phase. The entry price
depends polynomially on kappa/B and on the scaled small-step mass. -/
theorem eventually_initial_exceptional_attachment : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B c : ℝ, ∀ h I : List ℝ, InitialPhaseBudget A μ b T κ B h →
      2 ≤ c → B ≤ c → c ≤ κ → 1/32 ≤ 1-μ*c → (∀ t ∈ I, 1-μ*t ≠ 0) →
      ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V],
      ∀ m : ℕ, ∀ Q : SupportedPath V μ m, Q.x 0 ≠ 0 → Q.family.PositiveAt (Q.x 0) →
      Q.family.Gate (Q.x 0) (initialGateConstant/(κ/B)^2) →
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ initialPointRelativeConstant*(κ/B)*‖Q.x 0‖ ∧
        |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ initialSlopeRelativeConstant*(κ/B)*‖Q.x 0‖/κ) →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace (AttachmentSpace V ℂ) PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++((I++[c])++List.ofFn Q.steps) ∧
        J.x (Fin.last n) = retainedMap (W := PhaseSpace) (retainedMap (W := ℂ) (Q.x (Fin.last m))) ∧
        J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (initialGateConstant/(κ/B)^2) ∧
        (∀ k, |inner ℝ (unitDirection (J.x 0)) (J.family.z k)| ≤ initialPointRelativeConstant*(κ/B)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g k)| ≤ initialSlopeRelativeConstant*(κ/B)*‖J.x 0‖/κ) ∧
        ‖J.x 0‖ ≤ initialBlockConstant*(κ/B)^6*‖Q.x 0‖*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ) := by
  filter_upwards [eventually_initial_two_sided_attachment] with A hattach
  intro μ b T κ B c h I W hc hcB hcκ hqc hcritical V _ _ _ m Q hY hpositive hgate hqueries
  let K := κ/B
  have hK : 1 ≤ K := W.ratio_ge_one
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hV : 0 < ‖Q.x 0‖ := norm_pos_iff.mpr hY
  have hK2 : 1 ≤ K^2 := by nlinarith only [hK]
  have hη : 0 < initialGateConstant/K^2 := div_pos initialGateConstant_positive (sq_pos_of_pos hK0)
  have hη1 : initialGateConstant/K^2 ≤ 1 := (div_le_one (sq_pos_of_pos hK0)).mpr (initialGateConstant_le_one.trans hK2)
  have hM : 1 ≤ initialPointRelativeConstant*K := by
    have hh := mul_le_mul initialPointRelativeConstant_ge_one hK (by norm_num : (0 : ℝ) ≤ 1) initialPointRelativeConstant_positive.le
    simpa only [one_mul] using hh
  have hH : 0 ≤ initialSlopeRelativeConstant*K*‖Q.x 0‖/κ :=
    div_nonneg (mul_nonneg (mul_nonneg initialSlopeRelativeConstant_positive.le hK0.le) hV.le) W.kappa_positive.le
  have hμc : μ*c < 1 := by linarith only [hqc]
  have hminus : Q.family.Gate (Q.x 0) (-(initialGateConstant/K^2)) :=
    Q.family.gate_below hpositive.2 hgate (by linarith only [hη])
  obtain ⟨C,n₁,Q₁,hQ₁,hN₁,hend₁,hsteps₁,hz₁,hg₁⟩ := two_cone_attachment W.mu_positive hc hμc hV hM hH hη hη1
    I hcritical Q (unitDirection (Q.x 0)) (unitDirection_inner hY) (norm_smul_unitDirection hY).symm
    (fun j => (hqueries j).1) (fun j => (hqueries j).2) hgate hminus
  have hκKc : κ ≤ K*c := by
    have hh := mul_le_mul_of_nonneg_left hcB hK0.le
    have he : K*B = κ := by dsimp only [K]; field_simp [W.B_positive.ne']
    rwa [he] at hh
  have hsize := C.initial_radius_size W.mu_positive.le hc hcκ W.kappa_positive hK hV hκKc hqc
  let R := initialConeRadiusConstant*K^4*‖Q.x 0‖*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ)
  have htrace : C.traceRadius I ≤ R := C.initial_trace_radius W.mu_positive.le hc hcκ W.kappa_positive hK hV hκKc hqc I
  have hRbase : initialConeRadiusConstant*K^4*‖Q.x 0‖ ≤ R := by
    have he : 1 ≤ Real.exp (inverseCharge μ I) := Real.one_le_exp_iff.mpr (inverseCharge_nonneg μ I)
    have hs : 1 ≤ 1+smallPositiveSum μ I/κ := by have := div_nonneg (smallPositiveSum_nonneg μ I) W.kappa_positive.le; linarith
    have hh := mul_le_mul he hs (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos _).le
    have hcoef : 0 ≤ initialConeRadiusConstant*K^4*‖Q.x 0‖ := by have := initialConeRadiusConstant_positive; positivity
    have hm := mul_le_mul_of_nonneg_left hh hcoef
    dsimp only [R]
    nlinarith only [hm]
  let Z := C.traceRadius I+initialPointRelativeConstant*K*‖Q.x 0‖
  let H := 2*C.a+initialSlopeRelativeConstant*K*‖Q.x 0‖/κ
  have hZ0 : 0 ≤ Z := add_nonneg ((norm_nonneg _).trans hN₁)
    (mul_nonneg (mul_nonneg initialPointRelativeConstant_positive.le hK0.le) hV.le)
  have hH0 : 0 ≤ H := add_nonneg (by have := C.a_pos; positivity) hH
  have hZ : Z ≤ 2*R := by dsimp only [Z]; linarith only [htrace,hsize.2.2.1,hRbase]
  have hκH : κ*H ≤ 2*R := by
    have he : κ*(initialSlopeRelativeConstant*K*‖Q.x 0‖/κ) = initialSlopeRelativeConstant*K*‖Q.x 0‖ := by field_simp [W.kappa_positive.ne']
    dsimp only [H]
    rw [mul_add,he]
    linarith only [hsize.2.1,hsize.2.2.2,hRbase]
  obtain ⟨n₂,J,hsteps,hend,hNZ,hPos,hGate,hN,hrelative⟩ := hattach μ b T κ B h W (AttachmentSpace V ℂ) n₁ Q₁ hQ₁ Z H hZ0 hH0 hz₁ hg₁
  have hJnorm : ‖J.x 0‖ ≤ (1+5*initialEntryConstant)*K^2*R := initial_exceptional_norm_bound W.kappa_positive hK
    (norm_nonneg _) (norm_nonneg _) (hN₁.trans htrace) hZ hκH hN
  refine ⟨n₂,J,?_,?_,hNZ,hPos,hGate,hrelative,?_⟩
  · exact hsteps.trans (congrArg (fun l : List ℝ => (h++[b])++l) hsteps₁)
  · exact hend.trans (congrArg (retainedMap (W := PhaseSpace)) hend₁)
  · apply hJnorm.trans_eq
    unfold initialBlockConstant
    dsimp only [R,K]
    ring

end
end StrongSilver
