-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutPowerPadding
import StrongSilver.CutPowerCrudeUpper

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

def positivePartStep (φ : ℝ → ℝ) (b : ℝ) : ℝ := max (φ b) 0

theorem prefixMax_eq_sum_of_nonnegative (h : List ℝ) (hh : ∀ b ∈ h, 0 ≤ b) : prefixMax h = h.sum := by
  induction h with
  | nil => rfl
  | cons b h ih =>
    have hb := hh b (by simp)
    have ht : ∀ s ∈ h, 0 ≤ s := fun s hs => hh s (List.mem_cons_of_mem b hs)
    rw [prefixMax,ih ht,max_eq_right (add_nonneg hb (List.sum_nonneg ht)),List.sum_cons]

theorem gapPrefix_positivePart (φ : ℝ → ℝ) (h : List ℝ) :
    gapPrefix (positivePartStep φ) h = positiveMass (h.map φ) := by
  unfold gapPrefix
  rw [prefixMax_eq_sum_of_nonnegative _ (by
    intro b hb
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hb
    exact le_max_right _ _)]
  simp only [positiveMass,List.map_map,Function.comp_def,positivePartStep]
  rfl

theorem gapPrefix_le_positivePart (φ : ℝ → ℝ) (h : List ℝ) :
    gapPrefix φ h ≤ gapPrefix (positivePartStep φ) h := by
  rw [gapPrefix_positivePart]
  exact prefixMax_le_positiveMass _

/-- The positive-sum logarithmic observable L^S is at least L, including
the terminal reserve, whenever selected transformed pivots are positive. -/
theorem cutLogProduct_le_positivePart (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ)
    (C : ScheduleCut) (hselected : ∀ q ∈ C.phases, 0 ≤ φ q.pivot) :
    cutLogProduct φ P κ C ≤ cutLogProduct (positivePartStep φ) P κ C := by
  have hp := List.sum_le_sum (l := C.phases)
    (f := fun q => Real.log (gapPrefix φ q.gap+P))
    (g := fun q => Real.log (gapPrefix (positivePartStep φ) q.gap+P)) (fun q _ =>
      Real.log_le_log (add_pos_of_nonneg_of_pos (gapPrefix_nonnegative φ q.gap) hP)
        (add_le_add (gapPrefix_le_positivePart φ q.gap) le_rfl))
  have ht := Real.log_le_log
    (show 0 < gapPrefix φ C.terminal+P+κ by have hh := gapPrefix_nonnegative φ C.terminal; linarith only [hh,hP,hκ])
    (add_le_add (add_le_add (gapPrefix_le_positivePart φ C.terminal) le_rfl) le_rfl)
  have hsel : C.phases.map (fun q => Real.log (positivePartStep φ q.pivot-P)) =
      C.phases.map (fun q => Real.log (φ q.pivot-P)) := by
    apply List.map_congr_left
    intro q hq
    rw [positivePartStep,max_eq_left (hselected q hq)]
  simp only [cutLogProduct,cutMasses,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
    List.map_nil,List.sum_nil,List.map_map,Function.comp_def,add_zero]
  rw [hsel]
  linarith only [hp,ht]

theorem cutPower_le_positivePart (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 ≤ P) (hκ : 0 ≤ κ) (C : ScheduleCut) :
    cutPower φ P κ C ≤ cutPower (positivePartStep φ) P κ C := by
  rw [cutPower_eq_phase_sum,cutPower_eq_phase_sum]
  apply add_le_add
  · apply List.sum_le_sum
    intro q _
    exact Real.rpow_le_rpow (add_nonneg (gapPrefix_nonnegative φ q.gap) hP)
      (add_le_add (gapPrefix_le_positivePart φ q.gap) le_rfl) nu_positive.le
  · exact Real.rpow_le_rpow (add_nonneg (add_nonneg (gapPrefix_nonnegative φ C.terminal) hP) hκ)
      (add_le_add (add_le_add (gapPrefix_le_positivePart φ C.terminal) le_rfl) le_rfl) nu_positive.le

/-- Both actual signed-prefix and positive-sum masses have the same
absolute upper bound in terms of original positive unselected mass. -/
theorem positivePart_capped_gapPrefix_le_mass {μ B : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hcap : μ*B ≤ 1/2)
    (h : List ℝ) (hh : ∀ b ∈ h, b ≤ B) :
    gapPrefix (positivePartStep (cappedStep μ B)) h ≤ 2*positiveMass h := by
  rw [gapPrefix_positivePart]
  unfold positiveMass
  rw [List.map_map]
  have hs := List.sum_le_sum (l := h) (f := fun b => max (cappedStep μ B b) 0) (g := fun b => 2*max b 0)
    (fun b hb => cappedStep_positive_upper hμ hB hcap (hh b hb))
  simpa only [List.sum_map_mul_left,Function.comp_def] using hs

end
end StrongSilver
