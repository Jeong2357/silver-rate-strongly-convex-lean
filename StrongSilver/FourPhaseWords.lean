-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmallAbsoluteMassProduct
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

theorem absoluteMass_sublist_le {h k : List ℝ} (hk : h.Sublist k) : absoluteMass h ≤ absoluteMass k := by
  apply (hk.map abs).sum_le_sum
  intro x hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg b

theorem quadraticMultiplier_append (μ : ℝ) (h k : List ℝ) :
    quadraticMultiplier μ (h++k) = quadraticMultiplier μ h*quadraticMultiplier μ k := by
  simp only [quadraticMultiplier,List.map_append,List.prod_append]

namespace FourPhase

def phaseWord (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (i : Fin 4) : List ℝ := gap i++[pivot i]

def priorWord (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) : Fin 4 → List ℝ :=
  ![[],phaseWord gap pivot 0,phaseWord gap pivot 0++phaseWord gap pivot 1,
    phaseWord gap pivot 0++phaseWord gap pivot 1++phaseWord gap pivot 2]

def boundedWord (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) : List ℝ :=
  phaseWord gap pivot 0++phaseWord gap pivot 1++phaseWord gap pivot 2++gap 3

def carry (μ : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  quadraticMultiplier μ (priorWord gap pivot i)

theorem prior_gap_sublist_bounded (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (i : Fin 4) :
    (priorWord gap pivot i++gap i).Sublist (boundedWord gap pivot) := by
  unfold boundedWord
  simp only [List.append_assoc]
  have h0 : (gap 0).Sublist (phaseWord gap pivot 0) := List.sublist_append_left _ _
  have h1 : (gap 1).Sublist (phaseWord gap pivot 1) := List.sublist_append_left _ _
  have h2 : (gap 2).Sublist (phaseWord gap pivot 2) := List.sublist_append_left _ _
  fin_cases i
  · change ([]++gap 0).Sublist _
    simpa only [List.nil_append] using h0.trans (List.sublist_append_left _ _)
  · change (phaseWord gap pivot 0++gap 1).Sublist _
    exact (List.Sublist.refl _).append (h1.trans (List.sublist_append_left _ _))
  · change ((phaseWord gap pivot 0++phaseWord gap pivot 1)++gap 2).Sublist _
    have hh := (List.Sublist.refl (phaseWord gap pivot 0)).append
      ((List.Sublist.refl (phaseWord gap pivot 1)).append (h2.trans (List.sublist_append_left (phaseWord gap pivot 2) (gap 3))))
    simpa only [boundedWord,List.append_assoc] using hh
  · change ((phaseWord gap pivot 0++phaseWord gap pivot 1++phaseWord gap pivot 2)++gap 3).Sublist _
    simp only [List.append_assoc]
    exact List.Sublist.refl _

theorem carry_prefix_bounds {μ : ℝ} (hμ : 0 ≤ μ)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) (i : Fin 4) (k : ℕ) :
    1/2 ≤ carry μ gap pivot i*quadraticMultiplier μ ((gap i).take k) ∧
      carry μ gap pivot i*quadraticMultiplier μ ((gap i).take k) ≤ 2 := by
  have hsub : (priorWord gap pivot i++(gap i).take k).Sublist (boundedWord gap pivot) :=
    ((List.Sublist.refl _).append (List.take_sublist k (gap i))).trans (prior_gap_sublist_bounded gap pivot i)
  have hh := small_absolute_mass_product_bounds hμ (priorWord gap pivot i++(gap i).take k)
    ((mul_le_mul_of_nonneg_left (absoluteMass_sublist_le hsub) hμ).trans hsmall)
  simpa only [quadraticMultiplier_append,carry] using hh

end FourPhase
end
end StrongSilver
