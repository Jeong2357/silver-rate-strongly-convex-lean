-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLocalJoiningScale
import StrongSilver.FourPhaseJoiningBox

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2000000

/-- Original four-phase schedule with finite numerical versions of the
small-product assumptions in Lemma 4.1. -/
structure PhaseSchedule where
  μ : ℝ
  T : ℝ
  gap : Fin 4 → List ℝ
  pivot : Fin 4 → ℝ
  mu_positive : 0 < μ
  time_positive : 0 < T
  mu_upper : μ ≤ 1/4
  mu_time_upper : μ*T ≤ 1/4
  small_total : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4
  last_excess_lower : 1/2 ≤ lastExcess μ T gap pivot

namespace PhaseSchedule

def shape (S : PhaseSchedule) (ζ : ℝ) : Shape := productShape S.μ S.T S.gap S.pivot ζ
def k (S : PhaseSchedule) : ℝ := lastExcess S.μ S.T S.gap S.pivot

theorem k_positive (S : PhaseSchedule) : 0 < S.k := by
  have hh := S.last_excess_lower
  change 0 < lastExcess S.μ S.T S.gap S.pivot
  linarith only [hh]

theorem shape_coordinate_independent (S : PhaseSchedule) (ζ ζ' : ℝ) (i : Fin 8) (hi : i ≠ 7) :
    S.shape ζ i = S.shape ζ' i := by
  unfold shape productShape
  fin_cases i
  all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals first | exact False.elim (hi rfl) | rfl

def localParameters (S : PhaseSchedule) (ζ : ℝ) (hG : JoiningGeometry (S.shape ζ))
    (hz0 : 0 ≤ ζ) (hz16 : ζ ≤ 1/16) : LocalParameters where
  μ := S.μ
  T := S.T
  gap := S.gap
  pivot := S.pivot
  ζ := ζ
  mu_positive := S.mu_positive
  time_positive := S.time_positive
  small_total := S.small_total
  geometry := hG
  offset_nonnegative := hz0
  offset_upper := hz16

theorem localParameters_joining (S : PhaseSchedule) {ζ : ℝ} (hG : JoiningGeometry (S.shape ζ))
    (hz0 : 0 ≤ ζ) (hz16 : ζ ≤ 1/16) (hz60 : ζ ≤ 1/60) :
    (S.localParameters ζ hG hz0 hz16).JoiningScaleConditions :=
  ⟨S.mu_upper,S.mu_time_upper,S.last_excess_lower,hz60⟩

end PhaseSchedule

/-- Absolute perturbation radius supplies the full local input record.
Its geometric fields are proved, rather than assumed. -/
theorem exists_schedule_parameter_radius : ∃ δ > 0, δ ≤ 1/60 ∧ ∀ S : PhaseSchedule,
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
    (∀ i : Fin 8, i ≠ 7 → |S.shape 0 i-reference i| ≤ ε) →
    ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ δ → JoiningGeometry (S.shape ζ) := by
  obtain ⟨b,hb,hb16,hbox⟩ := exists_joining_box
  let δ := min b (1/60)
  have hδ : 0 < δ := lt_min hb (by norm_num)
  refine ⟨δ,hδ,min_le_right _ _,fun S ε hε hεδ hx ζ hz0 hzδ => hbox _ ?_⟩
  intro i
  by_cases hi : i = 7
  · subst i
    change |ζ-reference 7| ≤ b
    rw [reference_zeta,sub_zero,abs_of_nonneg hz0]
    exact hzδ.trans (min_le_left _ _)
  · rw [S.shape_coordinate_independent ζ 0 i hi]
    exact (hx i hi).trans (hεδ.trans (min_le_left _ _))

end
end StrongSilver.FourPhase
