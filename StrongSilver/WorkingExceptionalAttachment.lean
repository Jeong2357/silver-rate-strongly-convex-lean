-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingConeSize
import StrongSilver.TwoConeAttachment
import StrongSilver.WorkingTwoSidedAttachment
import StrongSilver.ExceptionalNormBound

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

/-- Traverse an arbitrary exceptional gap and a connecting selected step,
then attach its left phase. Every step is realized by a single admissible
finite-support trajectory. The common gate and relative projection bounds
are restored, with the polynomial entry cost used in Section 3.4.3. -/
theorem eventually_working_exceptional_attachment : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P c : ℝ, ∀ h I : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      2 ≤ c → c ≤ A^(2 : ℝ) → 1/32 ≤ 1-μ*c → (∀ t ∈ I, 1-μ*t ≠ 0) →
      ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V],
      ∀ m : ℕ, ∀ Q : SupportedPath V μ m, Q.x 0 ≠ 0 →
      Q.family.Gate (Q.x 0) (workingGateFraction A) →
      Q.family.Gate (Q.x 0) (-workingGateFraction A) →
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ A^(10 : ℝ)*‖Q.x 0‖ ∧
        |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ A^(10 : ℝ)*‖Q.x 0‖) →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace (AttachmentSpace V ℂ) PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++((I++[c])++List.ofFn Q.steps) ∧
        J.x (Fin.last n) = retainedMap (W := PhaseSpace) (retainedMap (W := ℂ) (Q.x (Fin.last m))) ∧
        J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (workingGateFraction A) ∧
        (∀ k, |inner ℝ (unitDirection (J.x 0)) (J.family.z k)| ≤ A^(10 : ℝ)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g k)| ≤ A^(10 : ℝ)*‖J.x 0‖) ∧
        ‖J.x 0‖ ≤ A^(25 : ℝ)*‖Q.x 0‖*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_working_cone_size,
    eventually_working_two_sided_attachment,eventually_exceptional_norm_bound]
    with A hA hsize hattach hnorm
  intro μ b T P c h I W hc hcA hqc hcritical V _ _ _ m Q hY hplus hminus hqueries
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hV : 0 < ‖Q.x 0‖ := norm_pos_iff.mpr hY
  have hM : 1 ≤ A^(10 : ℝ) := Real.one_le_rpow hA (by norm_num)
  have hH : 0 ≤ A^(10 : ℝ)*‖Q.x 0‖ := mul_nonneg (Real.rpow_pos_of_pos hA0 _).le hV.le
  have hη : 0 < workingGateFraction A := Real.rpow_pos_of_pos hA0 _
  have hη1 : workingGateFraction A ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num)
  have hμc : μ*c < 1 := by linarith only [hqc]
  obtain ⟨C,n₁,Q₁,hQ₁,hN₁,hend₁,hsteps₁,hz₁,hg₁⟩ := two_cone_attachment W.mu_positive hc hμc hV hM hH hη hη1
    I hcritical Q (unitDirection (Q.x 0)) (unitDirection_inner hY) (norm_smul_unitDirection hY).symm
    (fun j => (hqueries j).1) (fun j => (hqueries j).2) hplus hminus
  have hC := hsize μ c ‖Q.x 0‖ W.mu_positive.le (by linarith only [hc]) hcA hV hqc C
  let R := A^(14 : ℝ)*‖Q.x 0‖*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I)
  have htrace : C.traceRadius I ≤ R := C.traceRadius_bound_of_size W.mu_positive.le hC.1 hC.2 I
  have hRbase : A^(14 : ℝ)*‖Q.x 0‖ ≤ R := by
    have he : 1 ≤ Real.exp (inverseCharge μ I) := Real.one_le_exp_iff.mpr (inverseCharge_nonneg μ I)
    have hs : 1 ≤ 1+smallPositiveSum μ I := by linarith only [smallPositiveSum_nonneg μ I]
    have hh := mul_le_mul he hs (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos _).le
    have hm := mul_le_mul_of_nonneg_left hh hH
    have hm' := mul_le_mul_of_nonneg_left hh (mul_nonneg (Real.rpow_pos_of_pos hA0 (14 : ℝ)).le hV.le)
    dsimp only [R]
    nlinarith only [hm']
  have hMbase : A^(10 : ℝ)*‖Q.x 0‖ ≤ R := (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hA (by norm_num : (10 : ℝ) ≤ 14)) hV.le).trans hRbase
  let Z := C.traceRadius I+A^(10 : ℝ)*‖Q.x 0‖
  let H := 2*C.a+A^(10 : ℝ)*‖Q.x 0‖
  have hZ0 : 0 ≤ Z := add_nonneg ((norm_nonneg (Q₁.x 0)).trans hN₁) hH
  have hH0 : 0 ≤ H := add_nonneg (by have := C.a_pos; positivity) hH
  have hZ : Z ≤ 2*R := by dsimp only [Z]; linarith only [htrace,hMbase]
  have hHb : H ≤ 2*R := by dsimp only [H]; linarith only [hC.2,hRbase,hMbase]
  obtain ⟨e,he0,L,he,J,hsteps,hsource,hend,hNZ,hPos,hGate,hN,hrelative,hRatio⟩ :=
    hattach μ b T P h W (AttachmentSpace V ℂ) n₁ Q₁ hQ₁ Z H hZ0 hH0 hz₁ hg₁
  have hJnorm : ‖J.x 0‖ ≤ A^(11 : ℝ)*R := hnorm ‖J.x 0‖ ‖Q₁.x 0‖ Z H R
    (norm_nonneg _) (norm_nonneg _) (hN₁.trans htrace) hZ hHb hN
  refine ⟨_,J,?_,?_,hNZ,hPos,hGate,hrelative,?_⟩
  · exact hsteps.trans (congrArg (fun l : List ℝ => (h++[b])++l) hsteps₁)
  · exact hend.trans (congrArg (retainedMap (W := PhaseSpace)) hend₁)
  · apply hJnorm.trans_eq
    have hp : A^(11 : ℝ)*A^(14 : ℝ) = A^(25 : ℝ) := by rw [← Real.rpow_add hA0]; norm_num
    dsimp only [R]
    rw [← hp]
    ring

end
end StrongSilver
