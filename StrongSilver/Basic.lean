-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Problem
import Mathlib.Tactic

namespace StrongSilver
open Filter Set
open scoped Topology
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem admissible_iff_paper_class {κ : ℝ} {f : V → ℝ} {g : V → V} :
    Admissible κ f g ↔
      ConvexOn ℝ Set.univ (fun x => f x - (1 / κ) / 2 * ‖x‖ ^ 2) ∧
      (∀ x, HasGradientAt f (g x) x) ∧
      (∀ x y, ‖g x - g y‖ ≤ ‖x - y‖) := by
  constructor
  · intro h
    exact ⟨strongConvexOn_iff_convex.mp h.strong_convex, h.gradient, h.smooth⟩
  · rintro ⟨hc, hg, hl⟩
    exact ⟨strongConvexOn_iff_convex.mpr hc, hg, hl⟩

omit [CompleteSpace V] in
theorem strong_lower_at_min {μ : ℝ} {f : V → ℝ} {xstar : V}
    (hc : StrongConvexOn Set.univ μ f) (hm : ∀ x, f xstar ≤ f x) (x : V) :
    μ / 2 * ‖x - xstar‖ ^ 2 ≤ f x - f xstar := by
  let q : ℝ := μ / 2 * ‖x - xstar‖ ^ 2
  have hlim : Tendsto (fun t : ℝ => (1-t)*q) (𝓝[>] (0 : ℝ)) (𝓝 q) := by
    have hcont : Continuous (fun t : ℝ => (1-t)*q) := by fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    show Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) from
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with t ht ht1
  have ht0 : 0 < t := ht
  have ht1' : t < 1 := ht1
  have hconv := hc.2 (mem_univ xstar) (mem_univ x)
    (show 0 ≤ 1-t by linarith) ht0.le (show (1-t)+t=1 by ring)
  have hmin := hm ((1-t) • xstar + t • x)
  rw [norm_sub_rev] at hconv
  simp only [smul_eq_mul] at hconv
  apply (mul_le_mul_iff_right₀ ht0).mp
  dsimp [q]
  nlinarith only [hconv, hmin]

theorem value_gap_pos {κ : ℝ} (hκ : 0 < κ) (w : Instance κ) :
    0 < w.f w.start - w.f w.minimizer := by
  have hl := strong_lower_at_min w.admissible.strong_convex w.minimal w.start
  have hn : 0 < ‖w.start - w.minimizer‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr w.distinct))
  exact lt_of_lt_of_le (mul_pos (by positivity) hn) hl

@[simp] theorem iterate_nil {W : Type*} [AddCommGroup W] [Module ℝ W]
    (g : W → W) (x : W) : iterate [] g x = x := rfl

@[simp] theorem iterate_cons {W : Type*} [AddCommGroup W] [Module ℝ W]
    (a : ℝ) (h : List ℝ) (g : W → W) (x : W) :
    iterate (a :: h) g x = iterate h g (x - a • g x) := rfl

theorem iterate_append {W : Type*} [AddCommGroup W] [Module ℝ W]
    (h k : List ℝ) (g : W → W) (x : W) :
    iterate (h ++ k) g x = iterate k g (iterate h g x) := by
  exact List.foldl_append

theorem distance_error_nonneg {κ : ℝ} (h : List ℝ) (w : Instance κ) :
    0 ≤ distanceError h w := by
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem value_error_nonneg {κ : ℝ} (h : List ℝ) (w : Instance κ) :
    0 ≤ valueError h w := by
  exact div_nonneg (sub_nonneg.mpr (w.minimal _)) (sub_nonneg.mpr (w.minimal _))

theorem distance_error_le_D {κ : ℝ} (h : List ℝ) (w : Instance κ) :
    ENNReal.ofReal (distanceError h w) ≤ D κ h :=
  le_iSup (fun v : Instance κ => ENNReal.ofReal (distanceError h v)) w

theorem value_error_le_E {κ : ℝ} (h : List ℝ) (w : Instance κ) :
    ENNReal.ofReal (valueError h w) ≤ E κ h :=
  le_iSup (fun v : Instance κ => ENNReal.ofReal (valueError h v)) w

@[simp] theorem distance_error_nil {κ : ℝ} (w : Instance κ) : distanceError [] w = 1 := by
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr w.distinct)))

theorem value_error_nil {κ : ℝ} (hκ : 0 < κ) (w : Instance κ) : valueError [] w = 1 := by
  exact div_self (value_gap_pos hκ w).ne'

end
end StrongSilver
