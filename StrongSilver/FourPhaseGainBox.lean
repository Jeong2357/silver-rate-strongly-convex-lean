-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseGainDerivatives

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2500000

def dropOffset (x : Shape) : Shape := Function.update x 7 0

@[simp] theorem gain_dropOffset (x : Shape) : gain (dropOffset x) = gain x := by
  simp [gain,dropOffset,totalMass,leftMass,rightMass]
@[simp] theorem gainLeft_dropOffset (x : Shape) : gainLeft (dropOffset x) = gainLeft x := by
  simp [gainLeft,dropOffset,leftMass]
@[simp] theorem gainRight_dropOffset (x : Shape) : gainRight (dropOffset x) = gainRight x := by
  simp [gainRight,dropOffset,rightMass]
@[simp] theorem gainCoefficient_dropOffset (x : Shape) : gainCoefficient (dropOffset x) = gainCoefficient x := by
  simp [gainCoefficient,dropOffset,leftMass,totalTime,t0,t1,t2]

/-- Linear perturbation estimates for the gains and their coefficient.
The joining offset is unrestricted, since none of these quantities use it. -/
theorem exists_gain_box : ∃ C > 0, ∃ δ > 0, ∀ ε : ℝ,
    0 ≤ ε → ε ≤ δ → ∀ x : Shape,
    (∀ i : Fin 8, i ≠ 7 → |x i-reference i| ≤ ε) →
      |gain x| ≤ C*ε ∧ |gain x+gainLeft x+gainRight x| ≤ C*ε ∧
      |gainCoefficient x-1/Real.sqrt 2| ≤ C*ε := by
  obtain ⟨C₀,hC₀,d₀,hd₀,h₀⟩ := differentiable_box_bound differentiableAt_gain_reference
  obtain ⟨C₁,hC₁,d₁,hd₁,h₁⟩ := differentiable_box_bound differentiableAt_gainLeft_reference
  obtain ⟨C₂,hC₂,d₂,hd₂,h₂⟩ := differentiable_box_bound differentiableAt_gainRight_reference
  obtain ⟨C₃,hC₃,d₃,hd₃,h₃⟩ := differentiable_box_bound differentiableAt_gainCoefficient_reference
  let C := C₀+C₁+C₂+C₃
  let δ := min d₀ (min d₁ (min d₂ d₃))
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < δ := lt_min hd₀ (lt_min hd₁ (lt_min hd₂ hd₃))
  refine ⟨C,hC,δ,hδ,fun ε hε hεδ x hx => ?_⟩
  have hb : ∀ i, |dropOffset x i-reference i| ≤ ε := by
    intro i
    by_cases hi : i = 7
    · subst i
      simpa only [dropOffset,Function.update_self,reference_zeta,sub_self,abs_zero] using hε
    · simpa only [dropOffset,Function.update_of_ne hi] using hx i hi
  have hd0 : ε ≤ d₀ := hεδ.trans (min_le_left _ _)
  have hd1 : ε ≤ d₁ := hεδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd2 : ε ≤ d₂ := hεδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd3 : ε ≤ d₃ := hεδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hg := h₀ ε hε hd0 (dropOffset x) hb
  have hl := h₁ ε hε hd1 (dropOffset x) hb
  have hr := h₂ ε hε hd2 (dropOffset x) hb
  have hc := h₃ ε hε hd3 (dropOffset x) hb
  simp only [gain_dropOffset,gainLeft_dropOffset,gainRight_dropOffset,gainCoefficient_dropOffset,
    gains_reference.1,gains_reference.2.1,gains_reference.2.2,sub_zero,gainCoefficient_reference_sqrt] at hg hl hr hc
  have hCg : C₀ ≤ C := by dsimp [C]; linarith only [hC₁,hC₂,hC₃]
  have hCv : C₀+C₁+C₂ ≤ C := by dsimp [C]; linarith only [hC₃]
  have hCc : C₃ ≤ C := by dsimp [C]; linarith only [hC₀,hC₁,hC₂]
  refine ⟨hg.trans (mul_le_mul_of_nonneg_right hCg hε),?_,
    hc.trans (mul_le_mul_of_nonneg_right hCc hε)⟩
  calc
    _ ≤ |gain x|+|gainLeft x|+|gainRight x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C₀*ε+C₁*ε+C₂*ε := add_le_add (add_le_add hg hl) hr
    _ ≤ C*ε := by nlinarith only [mul_le_mul_of_nonneg_right hCv hε]

end
end StrongSilver.FourPhase
