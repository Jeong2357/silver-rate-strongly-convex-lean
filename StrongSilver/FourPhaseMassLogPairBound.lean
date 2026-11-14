-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseGainContDiff
import StrongSilver.FourPhaseGainBox
import StrongSilver.FourPhaseProductShape

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 1800000

/-- The normalization mass also has a pairwise logarithmic error of the
actual parameter difference, independently of the balance tolerance. -/
theorem exists_mass_log_pair_box : ∃ C > 0, ∃ δ > 0, ∀ x y : Shape,
    (∀ i, |x i-reference i| ≤ δ) → (∀ i, |y i-reference i| ≤ δ) →
    ∀ ε : ℝ, 0 ≤ ε → (∀ i, |x i-y i| ≤ ε) →
    |Real.log (totalMass x)-Real.log (totalMass y)| ≤ C*ε := by
  have hM : totalMass reference ≠ 0 := by
    rw [totalMass_reference]
    exact pow_ne_zero _ rho_positive.ne'
  have h : ContDiffAt ℝ 1 (fun x : Shape => Real.log (totalMass x)) reference :=
    contDiff_totalMass.contDiffAt.log hM
  exact contDiff_pair_box_bound h

@[simp] theorem totalMass_dropOffset (x : Shape) : totalMass (dropOffset x) = totalMass x := by
  simp [totalMass,leftMass,rightMass,dropOffset]

@[simp] theorem productShape_dropOffset (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (ζ : ℝ) :
    dropOffset (productShape μ T gap pivot ζ) = productShape μ T gap pivot 0 := by
  ext i
  by_cases hi : i = 7
  · subst i
    simp only [dropOffset,Function.update_self,productShape_offset]
  · change Function.update (productShape μ T gap pivot ζ) 7 0 i = _
    rw [Function.update_of_ne hi]
    unfold productShape
    fin_cases i
    all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
    all_goals first | exact False.elim (hi rfl) | rfl

@[simp] theorem gain_productShape_offset (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (ζ : ℝ) :
    gain (productShape μ T gap pivot ζ) = gain (productShape μ T gap pivot 0) := by
  rw [← productShape_dropOffset μ T gap pivot ζ,gain_dropOffset]

@[simp] theorem gainLeft_productShape_offset (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (ζ : ℝ) :
    gainLeft (productShape μ T gap pivot ζ) = gainLeft (productShape μ T gap pivot 0) := by
  rw [← productShape_dropOffset μ T gap pivot ζ,gainLeft_dropOffset]

@[simp] theorem gainRight_productShape_offset (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (ζ : ℝ) :
    gainRight (productShape μ T gap pivot ζ) = gainRight (productShape μ T gap pivot 0) := by
  rw [← productShape_dropOffset μ T gap pivot ζ,gainRight_dropOffset]

@[simp] theorem totalMass_productShape_offset (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (ζ : ℝ) :
    totalMass (productShape μ T gap pivot ζ) = totalMass (productShape μ T gap pivot 0) := by
  rw [← productShape_dropOffset μ T gap pivot ζ,totalMass_dropOffset]

end
end StrongSilver.FourPhase
