-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact

namespace StrongSilver
open Set Real
open scoped NNReal
noncomputable section

def tangentLine (f d : ℝ → ℝ) (s x : ℝ) : ℝ := f s+d s*(x-s)

theorem concave_tangent_upper {a b : ℝ} {f d : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc a b) f)
    (hd : ∀ s ∈ Icc a b, HasDerivWithinAt f (d s) (Icc a b) s)
    {s x : ℝ} (hs : s ∈ Icc a b) (hx : x ∈ Icc a b) : f x ≤ tangentLine f d s x := by
  have hc : ConvexOn ℝ (Icc a b) (fun x => -f x) := hf.neg
  rcases lt_trichotomy s x with hlt | he | hgt
  · have hh := hc.le_slope_of_hasDerivWithinAt hs hx hlt (hd s hs).neg
    simp only [slope,smul_eq_mul,vsub_eq_sub] at hh
    have hh' : -d s ≤ (-f x- -f s)/(x-s) := by convert hh using 1 <;> ring
    have hm := (le_div_iff₀ (sub_pos.mpr hlt)).mp hh'
    unfold tangentLine
    linarith
  · subst x
    simp only [tangentLine,sub_self,mul_zero,add_zero,le_refl]
  · have hh := hc.slope_le_of_hasDerivWithinAt hx hs hgt (hd s hs).neg
    simp only [slope,smul_eq_mul,vsub_eq_sub] at hh
    have hh' : (-f s- -f x)/(s-x) ≤ -d s := by convert hh using 1 <;> ring
    have hm := (div_le_iff₀ (sub_pos.mpr hgt)).mp hh'
    unfold tangentLine
    nlinarith only [hm]

def linearConcaveExtension (a b : ℝ) (f d : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < a then tangentLine f d a x else if b < x then tangentLine f d b x else f x

theorem linearConcaveExtension_on_interval {a b : ℝ} {f d : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc a b) :
    linearConcaveExtension a b f d x = f x := by
  simp only [linearConcaveExtension,not_lt.mpr hx.1,not_lt.mpr hx.2,if_false]

theorem linearConcaveExtension_left {a b : ℝ} (hab : a ≤ b) (f d : ℝ → ℝ) {x : ℝ} (hx : x ≤ a) :
    linearConcaveExtension a b f d x = tangentLine f d a x := by
  rcases lt_or_eq_of_le hx with hlt | rfl
  · simp only [linearConcaveExtension,hlt,if_true]
  · rw [linearConcaveExtension_on_interval ⟨le_rfl,hab⟩]
    simp only [tangentLine,sub_self,mul_zero,add_zero]

theorem linearConcaveExtension_right {a b : ℝ} (hab : a ≤ b) (f d : ℝ → ℝ) {x : ℝ} (hx : b ≤ x) :
    linearConcaveExtension a b f d x = tangentLine f d b x := by
  rcases lt_or_eq_of_le hx with hlt | rfl
  · simp only [linearConcaveExtension,not_lt.mpr (hab.trans hlt.le),if_false,hlt,if_true]
  · rw [linearConcaveExtension_on_interval ⟨hab,le_rfl⟩]
    simp only [tangentLine,sub_self,mul_zero,add_zero]

theorem linearConcaveExtension_active {a b : ℝ} (hab : a ≤ b) (f d : ℝ → ℝ) (x : ℝ) :
    ∃ s ∈ Icc a b, linearConcaveExtension a b f d x = tangentLine f d s x := by
  by_cases hx : x < a
  · exact ⟨a,⟨le_rfl,hab⟩,linearConcaveExtension_left hab f d hx.le⟩
  · by_cases hx' : b < x
    · exact ⟨b,⟨hab,le_rfl⟩,linearConcaveExtension_right hab f d hx'.le⟩
    · refine ⟨x,⟨le_of_not_gt hx,le_of_not_gt hx'⟩,?_⟩
      rw [linearConcaveExtension_on_interval ⟨le_of_not_gt hx,le_of_not_gt hx'⟩]
      simp only [tangentLine,sub_self,mul_zero,add_zero]

theorem linearConcaveExtension_le_tangent {a b : ℝ} (hab : a ≤ b) {f d : ℝ → ℝ}
    (htangent : ∀ s ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ tangentLine f d s x)
    (hanti : AntitoneOn d (Icc a b)) (x : ℝ) {s : ℝ} (hs : s ∈ Icc a b) :
    linearConcaveExtension a b f d x ≤ tangentLine f d s x := by
  by_cases hx : x < a
  · rw [linearConcaveExtension_left hab f d hx.le]
    have hh := htangent s hs a ⟨le_rfl,hab⟩
    have hd := mul_le_mul_of_nonpos_right (hanti ⟨le_rfl,hab⟩ hs hs.1) (sub_nonpos.mpr hx.le)
    unfold tangentLine at *
    nlinarith only [hh,hd]
  · by_cases hx' : b < x
    · rw [linearConcaveExtension_right hab f d hx'.le]
      have hh := htangent s hs b ⟨hab,le_rfl⟩
      have hd := mul_le_mul_of_nonneg_right (hanti hs ⟨hab,le_rfl⟩ hs.2) (sub_nonneg.mpr hx'.le)
      unfold tangentLine at *
      nlinarith only [hh,hd]
    · rw [linearConcaveExtension_on_interval ⟨le_of_not_gt hx,le_of_not_gt hx'⟩]
      exact htangent s hs x ⟨le_of_not_gt hx,le_of_not_gt hx'⟩

theorem linearConcaveExtension_concave {a b : ℝ} (hab : a ≤ b) {f d : ℝ → ℝ}
    (htangent : ∀ s ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ tangentLine f d s x)
    (hanti : AntitoneOn d (Icc a b)) : ConcaveOn ℝ univ (linearConcaveExtension a b f d) := by
  refine ⟨convex_univ,fun x hx y hy u v hu hv huv => ?_⟩
  simp only [smul_eq_mul]
  obtain ⟨s,hs,he⟩ := linearConcaveExtension_active hab f d (u*x+v*y)
  rw [he]
  have hhx := mul_le_mul_of_nonneg_left (linearConcaveExtension_le_tangent hab htangent hanti x hs) hu
  have hhy := mul_le_mul_of_nonneg_left (linearConcaveExtension_le_tangent hab htangent hanti y hs) hv
  have hid : u*tangentLine f d s x+v*tangentLine f d s y = tangentLine f d s (u*x+v*y) := by
    unfold tangentLine
    linear_combination (f s-d s*s)*huv
  linarith

theorem linearConcaveExtension_lipschitz {a b : ℝ} (hab : a ≤ b) {f d : ℝ → ℝ}
    (htangent : ∀ s ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ tangentLine f d s x)
    (hanti : AntitoneOn d (Icc a b)) (M : ℝ≥0) (hM : ∀ s ∈ Icc a b, |d s| ≤ M) :
    LipschitzWith M (linearConcaveExtension a b f d) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  obtain ⟨s,hs,he⟩ := linearConcaveExtension_active hab f d y
  have hh := linearConcaveExtension_le_tangent hab htangent hanti x hs
  have hd := mul_le_mul_of_nonneg_right (hM s hs) (abs_nonneg (x-y))
  have hi := (le_abs_self (d s*(x-y))).trans (by simpa only [abs_mul] using hd)
  rw [he,Real.dist_eq]
  unfold tangentLine at *
  linarith

end
end StrongSilver
