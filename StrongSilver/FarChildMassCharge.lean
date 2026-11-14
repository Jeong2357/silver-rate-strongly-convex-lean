-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BalancedChildMass
import StrongSilver.IndexedBalancedEdgeSpacing
import StrongSilver.VisibleOccurrenceBudget

namespace StrongSilver
open ScheduleTree Scalar.SignedIntervals ParentedScheduleNode
noncomputable section
set_option maxHeartbeats 4200000

def parentWeight (φ : ℝ → ℝ) (P : ℝ) (q : ParentedScheduleNode) : ℝ :=
  match q.parent with
  | none => 0
  | some p => Real.exp (nu*nodePaddedHeight φ P p)

def FarChildAt (φ : ℝ → ℝ) (P δ j width : ℝ) (q : ParentedScheduleNode) : Prop :=
  ∃ p : ScheduleNode, q.parent = some p ∧ PaddedBalanced φ P p.reserve δ p.source ∧ p.reserve = 0 ∧
    P ≤ (φ p.pivot-P)/4 ∧ j ≤ nodePaddedHeight φ P p ∧ nodePaddedHeight φ P p < j+1 ∧
    φ q.node.pivot ≤ P+Real.exp (j+1-width)

private theorem weight_from_positive_mass {height j mass : ℝ} (hj : j ≤ height)
    (hm : Real.exp height/2 ≤ mass) :
    Real.exp (nu*height) ≤ 2*Real.exp ((nu-1)*j)*mass := by
  have hm0 : 0 ≤ mass := (by positivity : (0:ℝ) ≤ Real.exp height/2).trans hm
  have h1 := mul_le_mul_of_nonneg_left (show Real.exp height ≤ 2*mass by linarith only [hm])
    (Real.exp_pos ((nu-1)*height)).le
  have h2 : Real.exp ((nu-1)*height) ≤ Real.exp ((nu-1)*j) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hj (by linarith only [nu_lt_one] : nu-1 ≤ 0))
  have h3 := mul_le_mul_of_nonneg_right h2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hm0)
  have he : Real.exp ((nu-1)*height)*Real.exp height = Real.exp (nu*height) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h1
  linear_combination h1+h3

/-- Far child intervals are distinct actual gaps at the shifted unit-bin
cutoff. Their parents' weights are paid by those gaps' positive mass. -/
theorem far_child_mass_charge (φ : ℝ → ℝ) (hφ : Monotone φ) {P κ δ j width : ℝ}
    (hP : 0 < P) (hzero : φ 0 ≤ 0) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4) (hwidth : 1 < width)
    (t : ScheduleTree) (hc : t.Cartesian) :
    (((parentedNodes 0 κ none t).filter fun q => @decide (FarChildAt φ P δ j width q) (Classical.propDecidable _)).map
      (parentWeight φ P)).sum ≤
      2*Real.exp ((nu-1)*j)*((indexedFrontier φ (P+Real.exp (j+1-width)) 0 κ t).map
        fun q => positiveMass (q.source.word.map φ)).sum := by
  classical
  have H := visible_occurrence_budget φ hφ (P+Real.exp (j+1-width)) κ t hc
    (fun q => decide (FarChildAt φ P δ j width q)) (parentWeight φ P)
    (fun q => 2*Real.exp ((nu-1)*j)*positiveMass (q.source.word.map φ))
    (fun q => mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (positiveMass_nonneg _)) (by
      intro q hq hsel
      obtain ⟨p,hparent,hbal,hres,hsmall,hlo,hhi,hchild⟩ := of_decide_eq_true hsel
      have hroot := hbal.root_positive
      have hExp : Real.exp (nodePaddedHeight φ P p) = φ p.pivot-P := Real.exp_log (sub_pos.mpr hroot)
      have hParent : P+Real.exp (j+1-width) < φ p.pivot := by
        have he := Real.exp_lt_exp.mpr (show j+1-width < nodePaddedHeight φ P p by linarith only [hlo,hwidth])
        rw [hExp] at he
        linarith only [he]
      refine ⟨⟨hchild,?_⟩,?_⟩
      · simpa only [parentAbove,hparent] using hParent
      · have hmass := actual_child_positive_mass (parentedNodes_actual_edge hq hparent) hP hzero hres hsmall hδ hδmax hbal
        have hmass' : Real.exp (nodePaddedHeight φ P p)/2 ≤ positiveMass (q.node.source.word.map φ) := by rwa [hExp]
        have hw := weight_from_positive_mass hlo hmass'
        simpa only [parentWeight,hparent] using hw)
  rw [List.sum_map_mul_left] at H
  exact H

end
end StrongSilver
