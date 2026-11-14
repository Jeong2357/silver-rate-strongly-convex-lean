-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedObservable

namespace StrongSilver
open ScheduleTree Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6400000

def linkedDynamicObservable (F : LinkedGap → ℝ → ℝ) (φ : ℝ → ℝ) (P : ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) (y : ℝ) : ℝ :=
  ((linkedFrontier φ (P+Real.exp y) start κ parent following t).map fun q => F q y).sum

theorem linkedDynamicObservable_measurable (F : LinkedGap → ℝ → ℝ) (hF : ∀ q, Measurable (F q))
    (φ : ℝ → ℝ) (P : ℝ) (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree) :
    Measurable (linkedDynamicObservable F φ P start κ parent following t) := by
  classical
  induction t generalizing start κ parent following with
  | leaf word =>
    have he : linkedDynamicObservable F φ P start κ parent following (.leaf word) = F ⟨⟨start,.leaf word,κ⟩,parent,following⟩ := by
      funext y
      simp [linkedDynamicObservable,linkedFrontier]
    rw [he]
    exact hF _
  | split l b r il ir =>
    let q : ScheduleNode := ⟨start,.split l b r,κ⟩
    have he : linkedDynamicObservable F φ P start κ parent following (.split l b r) = fun y =>
        if P+Real.exp y < φ b then
          linkedDynamicObservable F φ P start 0 (some q) (some q) l y+
          linkedDynamicObservable F φ P (start+l.word.length+1) κ (some q) following r y else F ⟨q,parent,following⟩ y := by
      funext y
      by_cases hy : P+Real.exp y < φ b <;> simp [linkedDynamicObservable,linkedFrontier,hy,q]
    rw [he]
    exact Measurable.ite ((isOpen_lt (continuous_const.add Real.continuous_exp) continuous_const).measurableSet)
      ((il start 0 (some q) (some q)).add (ir (start+l.word.length+1) κ (some q) following)) (hF _)

theorem linkedDynamicObservable_abs_upper (F : LinkedGap → ℝ → ℝ) (hF : ∀ q y, |F q y| ≤ 1)
    (φ : ℝ → ℝ) (P : ℝ) (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree) (y : ℝ) :
    |linkedDynamicObservable F φ P start κ parent following t y| ≤ (t.nodeCount:ℝ)+1 := by
  induction t generalizing start κ parent following with
  | leaf word =>
    simpa only [linkedDynamicObservable,linkedFrontier,List.map_singleton,List.sum_singleton,nodeCount,Nat.cast_zero,zero_add] using hF ⟨⟨start,.leaf word,κ⟩,parent,following⟩ y
  | split l b r il ir =>
    let q : ScheduleNode := ⟨start,.split l b r,κ⟩
    by_cases hb : P+Real.exp y < φ b
    · have he : linkedDynamicObservable F φ P start κ parent following (.split l b r) y =
          linkedDynamicObservable F φ P start 0 (some q) (some q) l y+
          linkedDynamicObservable F φ P (start+l.word.length+1) κ (some q) following r y := by
        simp only [linkedDynamicObservable,linkedFrontier,if_pos hb,List.map_append,List.sum_append,q]
      rw [he]
      have hl := il start 0 (some q) (some q)
      have hr := ir (start+l.word.length+1) κ (some q) following
      have hAbs := abs_add_le (linkedDynamicObservable F φ P start 0 (some q) (some q) l y)
        (linkedDynamicObservable F φ P (start+l.word.length+1) κ (some q) following r y)
      simp only [nodeCount,Nat.cast_add,Nat.cast_one]
      linear_combination hAbs+hl+hr
    · have he : linkedDynamicObservable F φ P start κ parent following (.split l b r) y = F ⟨q,parent,following⟩ y := by
        simp only [linkedDynamicObservable,linkedFrontier,if_neg hb,List.map_singleton,List.sum_singleton,q]
      rw [he]
      have hn : (0:ℝ) ≤ (ScheduleTree.split l b r).nodeCount := Nat.cast_nonneg _
      linarith only [hF ⟨q,parent,following⟩ y,hn]

/-- Finite linked gap indicators may depend measurably on the cutoff;
their total remains integrable without selecting an infinite family. -/
theorem linkedDynamicObservable_integrable (F : LinkedGap → ℝ → ℝ) (hFm : ∀ q, Measurable (F q))
    (hF : ∀ q y, |F q y| ≤ 1) (φ : ℝ → ℝ) (P : ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) (a b : ℝ) :
    IntervalIntegrable (linkedDynamicObservable F φ P start κ parent following t) volume a b := by
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound (by exact measure_Ioc_lt_top)
    (linkedDynamicObservable_measurable F hFm φ P start κ parent following t).aestronglyMeasurable.restrict ((t.nodeCount:ℝ)+1)
  exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using linkedDynamicObservable_abs_upper F hF φ P start κ parent following t y)

end
end StrongSilver
