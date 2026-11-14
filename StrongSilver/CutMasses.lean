-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScheduleCut
import StrongSilver.TransformedGapBudget
import StrongSilver.CappedTransform

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1400000

def gapPrefix (φ : ℝ → ℝ) (h : List ℝ) : ℝ := Scalar.SignedIntervals.prefixMax (h.map φ)

def cutMasses (φ : ℝ → ℝ) (P reserve : ℝ) (C : ScheduleCut) : List ℝ :=
  (C.phases.map fun q => gapPrefix φ q.gap+P)++[gapPrefix φ C.terminal+P+reserve]

def cutPower (φ : ℝ → ℝ) (P reserve : ℝ) (C : ScheduleCut) : ℝ :=
  ((cutMasses φ P reserve C).map fun x => x^nu).sum

def cutLogProduct (φ : ℝ → ℝ) (P reserve : ℝ) (C : ScheduleCut) : ℝ :=
  ((cutMasses φ P reserve C).map Real.log).sum-(C.phases.map fun q => Real.log (φ q.pivot-P)).sum

theorem gapPrefix_nonnegative (φ : ℝ → ℝ) (h : List ℝ) : 0 ≤ gapPrefix φ h := Scalar.SignedIntervals.prefixMax_nonneg _

theorem cutMasses_length (φ : ℝ → ℝ) (P reserve : ℝ) (C : ScheduleCut) :
    (cutMasses φ P reserve C).length = C.phases.length+1 := by simp [cutMasses]

theorem cutMasses_positive (φ : ℝ → ℝ) {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve) (C : ScheduleCut) :
    ∀ x ∈ cutMasses φ P reserve C, 0 < x := by
  intro x hx
  simp only [cutMasses,List.mem_append,List.mem_map,List.mem_singleton] at hx
  rcases hx with ⟨q,_,rfl⟩ | rfl
  · exact add_pos_of_nonneg_of_pos (gapPrefix_nonnegative φ q.gap) hP
  · have hh := gapPrefix_nonnegative φ C.terminal
    linarith only [hh,hP,hr]

theorem log_list_product (xs : List ℝ) (hxs : ∀ x ∈ xs, 0 < x) : Real.log xs.prod = (xs.map Real.log).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀ z ∈ xs, 0 < z := fun z hz => hxs z (List.mem_cons_of_mem x hz)
    rw [List.prod_cons,Real.log_mul hx.ne' (List.prod_pos ht).ne',ih ht]
    rfl

theorem cutLogProduct_eq_log_ratio (φ : ℝ → ℝ) {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve)
    (C : ScheduleCut) (hpiv : ∀ q ∈ C.phases, P < φ q.pivot) :
    cutLogProduct φ P reserve C =
      Real.log ((cutMasses φ P reserve C).prod/(C.phases.map fun q => φ q.pivot-P).prod) := by
  have hmass := cutMasses_positive φ hP hr C
  have hden : ∀ x ∈ C.phases.map (fun q => φ q.pivot-P), 0 < x := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact sub_pos.mpr (hpiv q hq)
  rw [Real.log_div (List.prod_pos hmass).ne' (List.prod_pos hden).ne',log_list_product _ hmass,log_list_product _ hden]
  simp only [cutLogProduct,List.map_map,Function.comp_apply]
  rfl

theorem capped_gapPrefix_eq {μ B : ℝ} (hμ : 0 < μ) (hcap : μ*B < 1) (h : List ℝ)
    (hh : ∀ b ∈ h, b ≤ B) : gapPrefix (cappedStep μ B) h = transformedGapMaximum μ h := by
  have hmap : h.map (cappedStep μ B) = h.map (logarithmicStep μ) := by
    apply List.map_congr_left
    intro b hb
    simp only [cappedStep,if_pos (hh b hb)]
  unfold gapPrefix
  rw [hmap]
  exact transformed_prefix_max hμ h (fun b hb => (mul_le_mul_of_nonneg_left (hh b hb) hμ.le).trans_lt hcap)

end
end StrongSilver
