-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BoundedODE
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace StrongSilver
open Set Metric
open scoped NNReal
noncomputable section

def clipHeight (L : ℝ) (x : ℝ) : ℝ := max 0 (min L x)

theorem clipHeight_lipschitz (L : ℝ) : LipschitzWith 1 (clipHeight L) :=
  (LipschitzWith.id.const_min L).const_max 0

theorem clipHeight_bounds {L : ℝ} (hL : 0 ≤ L) (x : ℝ) : 0 ≤ clipHeight L x ∧ clipHeight L x ≤ L :=
  ⟨le_max_left _ _,max_le hL (min_le_left _ _)⟩

theorem clipHeight_eq {L x : ℝ} (hx : 0 ≤ x) (hxL : x ≤ L) : clipHeight L x = x := by
  rw [clipHeight,min_eq_right hxL,max_eq_right hx]

theorem clipHeight_sq_lipschitz (L : ℝ≥0) : LipschitzWith (2*L) (fun x : ℝ => (clipHeight L x)^2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx := clipHeight_bounds L.coe_nonneg x
  have hy := clipHeight_bounds L.coe_nonneg y
  have hc := (clipHeight_lipschitz L).dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hc
  have hs : |clipHeight L x+clipHeight L y| ≤ 2*L := by
    rw [abs_of_nonneg (add_nonneg hx.1 hy.1)]
    linarith
  simp only [Real.dist_eq,NNReal.coe_mul,NNReal.coe_ofNat]
  calc
    _ = |(clipHeight L x-clipHeight L y)*(clipHeight L x+clipHeight L y)| := by congr 1; ring
    _ = |clipHeight L x-clipHeight L y| * |clipHeight L x+clipHeight L y| := abs_mul _ _
    _ ≤ |x-y| * (2*L) := mul_le_mul hc hs (abs_nonneg _) (abs_nonneg _)
    _ = _ := by ring

def clippedRiccati (r α β : ℝ → ℝ) (L : ℝ) (t x : ℝ) : ℝ :=
  r t+α t*clipHeight L x+β t*(clipHeight L x)^2

theorem clippedRiccati_lipschitz (r α β : ℝ → ℝ) (L A B : ℝ≥0) (t : ℝ)
    (hα : |α t| ≤ A) (hβ : |β t| ≤ B) :
    LipschitzWith (A+2*B*L) (clippedRiccati r α β L t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc := (clipHeight_lipschitz L).dist_le_mul x y
  have hs := (clipHeight_sq_lipschitz L).dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hc
  simp only [Real.dist_eq,NNReal.coe_mul,NNReal.coe_ofNat] at hs
  simp only [Real.dist_eq,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat]
  calc
    _ = |α t*(clipHeight L x-clipHeight L y)+β t*((clipHeight L x)^2-(clipHeight L y)^2)| := by
      unfold clippedRiccati
      congr 1
      ring
    _ ≤ |α t*(clipHeight L x-clipHeight L y)|+|β t*((clipHeight L x)^2-(clipHeight L y)^2)| := abs_add_le _ _
    _ = |α t| * |clipHeight L x-clipHeight L y|+|β t| * |(clipHeight L x)^2-(clipHeight L y)^2| := by
      rw [abs_mul,abs_mul]
    _ ≤ A*|x-y|+B*((2*L)*|x-y|) := by
      gcongr
    _ = _ := by ring

theorem clippedRiccati_bound (r α β : ℝ → ℝ) (L R A B : ℝ≥0) (t x : ℝ)
    (hr : |r t| ≤ R) (hα : |α t| ≤ A) (hβ : |β t| ≤ B) :
    |clippedRiccati r α β L t x| ≤ R+A*L+B*L^2 := by
  obtain ⟨hc0,hcL⟩ := clipHeight_bounds L.coe_nonneg x
  have hc : |clipHeight L x| ≤ L := by rwa [abs_of_nonneg hc0]
  have hs : |(clipHeight L x)^2| ≤ (L : ℝ)^2 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  unfold clippedRiccati
  calc
    _ ≤ |r t+α t*clipHeight L x|+|β t*(clipHeight L x)^2| := abs_add_le _ _
    _ ≤ |r t|+|α t*clipHeight L x|+|β t*(clipHeight L x)^2| := add_le_add (abs_add_le _ _) le_rfl
    _ = |r t|+|α t| * |clipHeight L x|+|β t| * |(clipHeight L x)^2| := by rw [abs_mul,abs_mul]
    _ ≤ _ := by gcongr

/-- Existence on a whole compact interval for the clipped scalar Riccati field.
The subsequent barrier argument must show that clipping is inactive. -/
theorem exists_clippedRiccati_terminal {a b : ℝ} (hab : a ≤ b) (r α β : ℝ → ℝ)
    (L R A B : ℝ≥0) (hrc : ContinuousOn r (Icc a b)) (hαc : ContinuousOn α (Icc a b))
    (hβc : ContinuousOn β (Icc a b))
    (hr : ∀ t ∈ Icc a b, |r t| ≤ R) (hα : ∀ t ∈ Icc a b, |α t| ≤ A)
    (hβ : ∀ t ∈ Icc a b, |β t| ≤ B) :
    ∃ J : ℝ → ℝ, J b = 0 ∧ ∀ t ∈ Icc a b,
      HasDerivWithinAt J (clippedRiccati r α β L t (J t)) (Icc a b) t := by
  apply exists_bounded_ode_terminal hab (clippedRiccati r α β L) (A+2*B*L) (R+A*L+B*L^2)
  · intro t ht
    exact clippedRiccati_lipschitz r α β L A B t (hα t ht) (hβ t ht)
  · intro x
    exact (hrc.add (hαc.mul_const _)).add (hβc.mul_const _)
  · intro t ht x
    simpa only [Real.norm_eq_abs,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow] using
      clippedRiccati_bound r α β L R A B t x (hr t ht) (hα t ht) (hβ t ht)

theorem exists_clippedRiccati_initial {a b : ℝ} (hab : a ≤ b) (r α β : ℝ → ℝ)
    (L R A B : ℝ≥0) (hrc : ContinuousOn r (Icc a b)) (hαc : ContinuousOn α (Icc a b))
    (hβc : ContinuousOn β (Icc a b))
    (hr : ∀ t ∈ Icc a b, |r t| ≤ R) (hα : ∀ t ∈ Icc a b, |α t| ≤ A)
    (hβ : ∀ t ∈ Icc a b, |β t| ≤ B) :
    ∃ J : ℝ → ℝ, J a = 0 ∧ ∀ t ∈ Icc a b,
      HasDerivWithinAt J (clippedRiccati r α β L t (J t)) (Icc a b) t := by
  apply exists_bounded_ode_initial hab (clippedRiccati r α β L) (A+2*B*L) (R+A*L+B*L^2)
  · intro t ht
    exact clippedRiccati_lipschitz r α β L A B t (hα t ht) (hβ t ht)
  · intro x
    exact (hrc.add (hαc.mul_const _)).add (hβc.mul_const _)
  · intro t ht x
    simpa only [Real.norm_eq_abs,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow] using
      clippedRiccati_bound r α β L R A B t x (hr t ht) (hα t ht) (hβ t ht)

end
end StrongSilver
