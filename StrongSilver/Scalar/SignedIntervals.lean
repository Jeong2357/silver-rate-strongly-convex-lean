-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Tactic

/-! Signed interval identities (arcs.tex eq:mass-defs; bands.tex lem:intervals).
The empty prefix is included by definition. All results quantify over arbitrary
real schedules, including empty schedules and negative steps. -/
namespace StrongSilver.Scalar.SignedIntervals

def positiveMass (h : List ℝ) : ℝ := (h.map fun x => max x 0).sum
def negativeMass (h : List ℝ) : ℝ := (h.map fun x => max (-x) 0).sum
def prefixMax : List ℝ → ℝ
  | [] => 0
  | a :: h => max 0 (a + prefixMax h)
def drawdown (h : List ℝ) : ℝ := prefixMax h - h.sum

theorem prefixMax_nonneg (h : List ℝ) : 0 ≤ prefixMax h := by
  cases h with
  | nil => exact le_rfl
  | cons a h => exact le_max_left _ _

theorem sum_le_prefixMax (h : List ℝ) : h.sum ≤ prefixMax h := by
  induction h with
  | nil => exact le_rfl
  | cons a h ih =>
    exact (add_le_add le_rfl ih).trans (le_max_right _ _)

theorem prefixMax_le_positiveMass (h : List ℝ) : prefixMax h ≤ positiveMass h := by
  induction h with
  | nil => simp [prefixMax, positiveMass]
  | cons a h ih =>
    have ha : a ≤ max a 0 := le_max_left _ _
    have hb : 0 ≤ max a 0 := le_max_right _ _
    have hc := prefixMax_nonneg h
    simp only [prefixMax, positiveMass, List.map_cons, List.sum_cons] at *
    exact max_le (by linarith) (by linarith)

theorem positiveMass_nonneg (h : List ℝ) : 0 ≤ positiveMass h :=
  (prefixMax_nonneg h).trans (prefixMax_le_positiveMass h)

theorem drawdown_nonneg (h : List ℝ) : 0 ≤ drawdown h :=
  sub_nonneg.mpr (sum_le_prefixMax h)

theorem positiveMass_append (a b : List ℝ) :
    positiveMass (a ++ b) = positiveMass a + positiveMass b := by
  simp [positiveMass]

theorem prefixMax_append (a b : List ℝ) :
    prefixMax (a ++ b) = max (prefixMax a) (a.sum + prefixMax b) := by
  induction a with
  | nil => simp [prefixMax, max_eq_right (prefixMax_nonneg b)]
  | cons x a ih =>
    simp only [List.cons_append, prefixMax, ih, List.sum_cons, add_max,
      max_assoc, add_assoc]

theorem prefix_sum_le_prefixMax (a h : List ℝ) (ha : a.IsPrefix h) :
    a.sum ≤ prefixMax h := by
  obtain ⟨b, rfl⟩ := List.prefix_iff_exists_eq_append.mp ha
  rw [prefixMax_append]
  exact (sum_le_prefixMax a).trans (le_max_left _ _)

theorem prefixMax_attained (h : List ℝ) :
    ∃ a : List ℝ, a.IsPrefix h ∧ a.sum = prefixMax h := by
  induction h with
  | nil => exact ⟨[], List.prefix_refl [], rfl⟩
  | cons x h ih =>
    obtain ⟨a, ha, he⟩ := ih
    by_cases hx : 0 ≤ x + prefixMax h
    · obtain ⟨b, hb⟩ := List.prefix_iff_exists_eq_append.mp ha
      refine ⟨x :: a, ?_, ?_⟩
      · exact ⟨b, by simp [hb]⟩
      · simp [prefixMax, max_eq_right hx, he]
    · refine ⟨[], List.nil_prefix, ?_⟩
      simp [prefixMax, max_eq_left (le_of_not_ge hx)]

theorem max_plus_split (a b : List ℝ) (h : ℝ) :
    prefixMax (a ++ h :: b) =
      prefixMax a + max 0 (h + prefixMax b - drawdown a) := by
  have ha := sum_le_prefixMax a
  rw [prefixMax_append]
  simp only [prefixMax, drawdown, add_max, add_zero]
  rw [← max_assoc, max_eq_left ha]
  congr 1
  ring

theorem deficit_le_append_right (a b : List ℝ) :
    positiveMass a - prefixMax a ≤ positiveMass (a ++ b) - prefixMax (a ++ b) := by
  have h1 := sum_le_prefixMax a
  have h2 := prefixMax_le_positiveMass b
  have h3 := positiveMass_nonneg b
  rw [positiveMass_append, prefixMax_append]
  have : max (prefixMax a) (a.sum + prefixMax b) ≤ prefixMax a + positiveMass b :=
    max_le (by linarith) (by linarith)
  linarith

theorem deficit_le_append_left (a b : List ℝ) :
    positiveMass b - prefixMax b ≤ positiveMass (a ++ b) - prefixMax (a ++ b) := by
  have h1 := (sum_le_prefixMax a).trans (prefixMax_le_positiveMass a)
  have h2 := prefixMax_le_positiveMass a
  have h3 := prefixMax_nonneg b
  rw [positiveMass_append, prefixMax_append]
  have : max (prefixMax a) (a.sum + prefixMax b) ≤ positiveMass a + prefixMax b :=
    max_le (by linarith) (by linarith)
  linarith

theorem interval_deficit_mono (before interval after : List ℝ) :
    positiveMass interval - prefixMax interval ≤
    positiveMass (before ++ interval ++ after) - prefixMax (before ++ interval ++ after) :=
  (deficit_le_append_left before interval).trans (deficit_le_append_right _ after)

theorem suffix_drawdown_mono (before suffix : List ℝ) :
    drawdown suffix ≤ drawdown (before ++ suffix) := by
  simp only [drawdown, prefixMax_append, List.sum_append]
  have := le_max_right (prefixMax before) (before.sum + prefixMax suffix)
  linarith

theorem negativeMass_identity (h : List ℝ) :
    negativeMass h = (positiveMass h - prefixMax h) + drawdown h := by
  suffices negativeMass h = positiveMass h - h.sum by
    simp only [drawdown]
    linarith
  induction h with
  | nil => simp [negativeMass, positiveMass]
  | cons a h ih =>
    simp only [negativeMass, positiveMass, List.map_cons, List.sum_cons] at *
    by_cases ha : 0 ≤ a
    · rw [max_eq_right (by linarith : -a ≤ 0), max_eq_left ha]
      linarith
    · rw [max_eq_left (by linarith : 0 ≤ -a), max_eq_right (le_of_not_ge ha)]
      linarith

theorem record_reset (a b : List ℝ) (h : ℝ) (hh : drawdown a < h) :
    prefixMax (a ++ h :: b) = prefixMax a + h - drawdown a + prefixMax b ∧
    drawdown (a ++ h :: b) = drawdown b := by
  have hb := prefixMax_nonneg b
  have hp : 0 ≤ h + prefixMax b - drawdown a := by linarith
  have hm := max_plus_split a b h
  rw [max_eq_right hp] at hm
  constructor
  · linarith
  · simp only [drawdown, List.sum_append, List.sum_cons] at *
    linarith

end StrongSilver.Scalar.SignedIntervals
