-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseGainContDiff

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 1800000

/-- Absolute pairwise perturbation constants for comparing the actual
product-time gains with the exact rescaled Cartesian masses. -/
theorem exists_gain_pair_box : ∃ C > 0, ∃ δ > 0, ∀ x y : Shape,
    (∀ i, |x i-reference i| ≤ δ) → (∀ i, |y i-reference i| ≤ δ) →
    ∀ ε : ℝ, 0 ≤ ε → (∀ i, |x i-y i| ≤ ε) →
    |gain x-gain y|+|gainLeft x-gainLeft y|+|gainRight x-gainRight y| ≤ C*ε := by
  obtain ⟨C₀,hC₀,d₀,hd₀,h₀⟩ := contDiff_pair_box_bound contDiffAt_gain_reference
  obtain ⟨C₁,hC₁,d₁,hd₁,h₁⟩ := contDiff_pair_box_bound contDiffAt_gainLeft_reference
  obtain ⟨C₂,hC₂,d₂,hd₂,h₂⟩ := contDiff_pair_box_bound contDiffAt_gainRight_reference
  let C := C₀+C₁+C₂
  let δ := min d₀ (min d₁ d₂)
  refine ⟨C,by dsimp [C]; linarith only [hC₀,hC₁,hC₂],δ,lt_min hd₀ (lt_min hd₁ hd₂),?_⟩
  intro x y hx hy ε hε hxy
  have hd0 : δ ≤ d₀ := min_le_left _ _
  have hd1 : δ ≤ d₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hd2 : δ ≤ d₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hg := h₀ x y (fun i => (hx i).trans hd0) (fun i => (hy i).trans hd0) ε hε hxy
  have hl := h₁ x y (fun i => (hx i).trans hd1) (fun i => (hy i).trans hd1) ε hε hxy
  have hr := h₂ x y (fun i => (hx i).trans hd2) (fun i => (hy i).trans hd2) ε hε hxy
  dsimp only [C]
  nlinarith only [hg,hl,hr]

end
end StrongSilver.FourPhase
