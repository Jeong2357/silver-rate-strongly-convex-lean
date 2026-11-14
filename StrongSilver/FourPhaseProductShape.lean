-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseProductBounds

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2500000

def normalizedMass (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  queryTime μ T (carry μ gap pivot i) (minPrefixProduct μ (gap i))

def normalizedExcess (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  (1-μ)*(1-quadraticMultiplier μ (phaseWord gap pivot i.castSucc))/(μ*T*carry μ gap pivot i.succ)-
    normalizedMass μ T gap pivot i.castSucc

def lastExcess (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) : ℝ :=
  (1-quadraticMultiplier μ (phaseWord gap pivot 3)/minPrefixProduct μ (gap 3))/(μ*T)-1/T

/-- The normalized coordinates in Lemma 4.1, obtained from the original
signed schedule and its actual prefix products. -/
def productShape (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (ζ : ℝ) : Shape :=
  ![normalizedMass μ T gap pivot 0,normalizedMass μ T gap pivot 1,
    normalizedMass μ T gap pivot 2,normalizedMass μ T gap pivot 3,
    normalizedExcess μ T gap pivot 0,normalizedExcess μ T gap pivot 1,
    normalizedExcess μ T gap pivot 2,ζ]

theorem productShape_mass (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (ζ : ℝ) (i : Fin 4) :
    phaseMass (productShape μ T gap pivot ζ) i = normalizedMass μ T gap pivot i := by
  fin_cases i <;> rfl

theorem productShape_excess (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (ζ : ℝ) (i : Fin 3) :
    phaseExcess (productShape μ T gap pivot ζ) i = normalizedExcess μ T gap pivot i := by
  fin_cases i <;> rfl

@[simp] theorem productShape_offset (μ T : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (ζ : ℝ) :
    productShape μ T gap pivot ζ 7 = ζ := rfl

variable {μ T : ℝ} (hμ : 0 < μ) (hT : 0 < T) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4)
include hμ hT hsmall

theorem productShape_orbit_next (ζ : ℝ) (i : Fin 3) :
    phaseState μ T (carry μ gap pivot i.castSucc)
      (phaseStart (productShape μ T gap pivot ζ) i.castSucc)
      (slope (productShape μ T gap pivot ζ) i.castSucc)
      (quadraticMultiplier μ (phaseWord gap pivot i.castSucc)) =
    carry μ gap pivot i.succ • phaseStart (productShape μ T gap pivot ζ) i.succ := by
  rw [carry_recurrence]
  apply orbit_phase_next hμ.ne' hT.ne'
    (carry_positive hμ.le gap pivot hsmall i.castSucc).ne'
    (first_phase_product_positive hμ.le gap pivot hsmall i).ne' i
  rw [productShape_excess,productShape_mass]
  unfold normalizedExcess
  rw [carry_recurrence]

theorem productShape_orbit_ray (ζ : ℝ) (i : Fin 4) (k : ℕ) :
    let x := productShape μ T gap pivot ζ
    let c := quadraticMultiplier μ ((gap i).take k)
    let s := phaseMass x i-queryTime μ T (carry μ gap pivot i) c
    0 ≤ s ∧ phaseState μ T (carry μ gap pivot i) (phaseStart x i) (slope x i) c-(1/T) • slope x i =
      (carry μ gap pivot i*c) • (foot x i+s • slope x i) := by
  dsimp only
  apply orbit_query_ray hμ hT (carry_positive hμ.le gap pivot hsmall i) i (gap i)
    (gap_small_steps hμ.le gap pivot hsmall i)
  exact productShape_mass μ T gap pivot ζ i

end
end StrongSilver.FourPhase
