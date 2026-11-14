-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseWords
import StrongSilver.FourPhaseOrbitQueries

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2200000

theorem minPrefixProduct_attained (μ : ℝ) (h : List ℝ) :
    ∃ k : ℕ, k ≤ h.length ∧ minPrefixProduct μ h = quadraticMultiplier μ (h.take k) := by
  induction h with
  | nil => exact ⟨0,le_refl _,rfl⟩
  | cons b h ih =>
    obtain ⟨k,hk,he⟩ := ih
    by_cases hm : 1 ≤ (1-μ*b)*minPrefixProduct μ h
    · refine ⟨0,by omega,?_⟩
      exact min_eq_left hm
    · refine ⟨k+1,by simp only [List.length_cons]; omega,?_⟩
      change min 1 ((1-μ*b)*minPrefixProduct μ h) = (1-μ*b)*quadraticMultiplier μ (h.take k)
      rw [min_eq_right (le_of_not_ge hm),he]

namespace FourPhase

theorem carry_recurrence (μ : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (i : Fin 3) :
    carry μ gap pivot i.succ = carry μ gap pivot i.castSucc*quadraticMultiplier μ (phaseWord gap pivot i.castSucc) := by
  fin_cases i
  · change quadraticMultiplier μ (phaseWord gap pivot 0) = quadraticMultiplier μ []*quadraticMultiplier μ (phaseWord gap pivot 0)
    simp [quadraticMultiplier]
  · exact quadraticMultiplier_append μ _ _
  · change quadraticMultiplier μ (phaseWord gap pivot 0++phaseWord gap pivot 1++phaseWord gap pivot 2) =
        quadraticMultiplier μ (phaseWord gap pivot 0++phaseWord gap pivot 1)*quadraticMultiplier μ (phaseWord gap pivot 2)
    exact quadraticMultiplier_append μ _ _

variable {μ : ℝ} (hμ : 0 ≤ μ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4)
include hμ hsmall

theorem carry_positive (i : Fin 4) : 0 < carry μ gap pivot i := by
  have hh := (carry_prefix_bounds hμ gap pivot hsmall i 0).1
  have he : quadraticMultiplier μ ((gap i).take 0) = 1 := rfl
  rw [he,mul_one] at hh
  linarith only [hh]

theorem gap_small_steps (i : Fin 4) : ∀ b ∈ gap i, μ*b < 1 := by
  have hsub : (gap i).Sublist (boundedWord gap pivot) :=
    (List.sublist_append_right _ _).trans (prior_gap_sublist_bounded gap pivot i)
  have hs := (mul_le_mul_of_nonneg_left (absoluteMass_sublist_le hsub) hμ).trans hsmall
  exact small_absolute_mass_steps hμ (gap i) (by linarith only [hs])

theorem carry_minimum_bounds (i : Fin 4) :
    1/2 ≤ carry μ gap pivot i*minPrefixProduct μ (gap i) ∧
    carry μ gap pivot i*minPrefixProduct μ (gap i) ≤ 2 := by
  obtain ⟨k,hk,he⟩ := minPrefixProduct_attained μ (gap i)
  rw [he]
  exact carry_prefix_bounds hμ gap pivot hsmall i k

theorem first_phase_product_positive (i : Fin 3) :
    0 < quadraticMultiplier μ (phaseWord gap pivot i.castSucc) := by
  have h0 := carry_positive hμ gap pivot hsmall i.castSucc
  have h1 := carry_positive hμ gap pivot hsmall i.succ
  rw [carry_recurrence] at h1
  exact (mul_pos_iff.mp h1).resolve_right (fun hh => (not_lt_of_ge h0.le) hh.1) |>.2

end FourPhase
end
end StrongSilver
