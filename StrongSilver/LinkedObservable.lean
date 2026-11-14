-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFrontier
import StrongSilver.CutObservables

namespace StrongSilver
open ScheduleTree Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5800000

def linkedObservable (F : LinkedGap → ℝ) (φ : ℝ → ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) (s : ℝ) : ℝ :=
  ((linkedFrontier φ s start κ parent following t).map F).sum

def linkedObservableBound (F : LinkedGap → ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) : ScheduleTree → ℝ
  | t@(.leaf _) => |F ⟨⟨start,t,κ⟩,parent,following⟩|
  | t@(.split l _ r) =>
    let q : ScheduleNode := ⟨start,t,κ⟩
    |F ⟨q,parent,following⟩|+linkedObservableBound F start 0 (some q) (some q) l+
      linkedObservableBound F (start+l.word.length+1) κ (some q) following r

theorem linkedObservableBound_nonnegative (F : LinkedGap → ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) :
    0 ≤ linkedObservableBound F start κ parent following t := by
  induction t generalizing start κ parent following with
  | leaf word => exact abs_nonneg _
  | split l b r il ir => exact add_nonneg (add_nonneg (abs_nonneg _) (il _ _ _ _)) (ir _ _ _ _)

theorem linkedObservable_abs_upper (F : LinkedGap → ℝ) (φ : ℝ → ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) (s : ℝ) :
    |linkedObservable F φ start κ parent following t s| ≤ linkedObservableBound F start κ parent following t := by
  induction t generalizing start κ parent following with
  | leaf word => simp [linkedObservable,linkedFrontier,linkedObservableBound]
  | split l b r il ir =>
    let q : ScheduleNode := ⟨start,.split l b r,κ⟩
    have hl := il start 0 (some q) (some q)
    have hr := ir (start+l.word.length+1) κ (some q) following
    have hln := linkedObservableBound_nonnegative F start 0 (some q) (some q) l
    have hrn := linkedObservableBound_nonnegative F (start+l.word.length+1) κ (some q) following r
    by_cases hb : s < φ b
    · have he : linkedObservable F φ start κ parent following (.split l b r) s =
          linkedObservable F φ start 0 (some q) (some q) l s+
          linkedObservable F φ (start+l.word.length+1) κ (some q) following r s := by
        simp only [linkedObservable,linkedFrontier,if_pos hb,List.map_append,List.sum_append,q]
      rw [he]
      have habs := abs_add_le (linkedObservable F φ start 0 (some q) (some q) l s)
        (linkedObservable F φ (start+l.word.length+1) κ (some q) following r s)
      change _ ≤ |F ⟨q,parent,following⟩|+_+_
      linear_combination habs+hl+hr+abs_nonneg (F ⟨q,parent,following⟩)
    · have he : linkedObservable F φ start κ parent following (.split l b r) s = F ⟨q,parent,following⟩ := by
        simp only [linkedObservable,linkedFrontier,if_neg hb,List.map_singleton,List.sum_singleton,q]
      rw [he]
      change _ ≤ |F ⟨q,parent,following⟩|+_+_
      linarith only [hln,hrn]

theorem linkedObservable_measurable (F : LinkedGap → ℝ) (φ : ℝ → ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) :
    Measurable (linkedObservable F φ start κ parent following t) := by
  classical
  induction t generalizing start κ parent following with
  | leaf word =>
    have he : linkedObservable F φ start κ parent following (.leaf word) =
        fun _ : ℝ => F ⟨⟨start,.leaf word,κ⟩,parent,following⟩ := by
      funext s
      simp [linkedObservable,linkedFrontier]
    rw [he]
    exact measurable_const
  | split l b r il ir =>
    let q : ScheduleNode := ⟨start,.split l b r,κ⟩
    have hi : Measurable (fun s : ℝ => if s < φ b then
        linkedObservable F φ start 0 (some q) (some q) l s+
        linkedObservable F φ (start+l.word.length+1) κ (some q) following r s else F ⟨q,parent,following⟩) :=
      Measurable.ite (p:=fun s : ℝ => s < φ b) measurableSet_Iio
      ((il start 0 (some q) (some q)).add (ir (start+l.word.length+1) κ (some q) following))
      (show Measurable (fun _ : ℝ => F ⟨q,parent,following⟩) from measurable_const)
    have he : linkedObservable F φ start κ parent following (.split l b r) =
        fun s : ℝ => if s < φ b then
          linkedObservable F φ start 0 (some q) (some q) l s+
          linkedObservable F φ (start+l.word.length+1) κ (some q) following r s else F ⟨q,parent,following⟩ := by
      funext s
      by_cases hs : s < φ b <;> simp [linkedObservable,linkedFrontier,hs,q]
    rw [he]
    exact hi

/-- Every real observable of the finite linked frontier is integrable
after a measurable reparameterization of the cutoff. -/
theorem linkedObservable_integrable (F : LinkedGap → ℝ) (φ : ℝ → ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) (q : ℝ → ℝ) (hq : Measurable q) (a b : ℝ) :
    IntervalIntegrable (fun y => linkedObservable F φ start κ parent following t (q y)) volume a b := by
  have hm := (linkedObservable_measurable F φ start κ parent following t).comp hq
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound (by exact measure_Ioc_lt_top) hm.aestronglyMeasurable.restrict (linkedObservableBound F start κ parent following t)
  exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs,Function.comp_apply] using linkedObservable_abs_upper F φ start κ parent following t (q y))

end
end StrongSilver
