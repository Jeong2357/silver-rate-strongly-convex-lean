-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.MoreauEpigraph

namespace StrongSilver.Moreau
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

def minimizingPair (P : Epigraph E) (x : E) : E × ℝ := (exists_minimizer P x).choose
def proximal (P : Epigraph E) (x : E) : E := (minimizingPair P x).1
def gradient (P : Epigraph E) (x : E) : E := x-proximal P x
def envelope (P : Epigraph E) (x : E) : ℝ := objective x (minimizingPair P x)

theorem minimizingPair_mem (P : Epigraph E) (x : E) : minimizingPair P x ∈ P.carrier :=
  (exists_minimizer P x).choose_spec.1

theorem minimizingPair_min (P : Epigraph E) (x : E) (q : E × ℝ) (hq : q ∈ P.carrier) :
    envelope P x ≤ objective x q := (exists_minimizer P x).choose_spec.2 q hq

theorem minimizingPair_supports (P : Epigraph E) (x : E) :
    Supports P (proximal P x) (minimizingPair P x).2 (gradient P x) :=
  minimizer_supports P x _ (minimizingPair_mem P x) (minimizingPair_min P x)

theorem minimizingPair_eq_of_supports (P : Epigraph E) (x z : E) (t : ℝ)
    (h : Supports P z t (x-z)) : minimizingPair P x = (z,t) :=
  minimizer_unique P x _ _ (minimizingPair_mem P x) h.1
    (minimizingPair_min P x) (supports_minimizer P x z t h)

theorem envelope_nonnegative (P : Epigraph E) (x : E) : 0 ≤ envelope P x :=
  objective_nonnegative P x _ (minimizingPair_mem P x)

theorem envelope_zero (P : Epigraph E) : envelope P 0 = 0 := by
  apply le_antisymm _ (envelope_nonnegative P 0)
  simpa [objective] using minimizingPair_min P 0 (0,0) P.zero_mem

theorem objective_shift_identity (x y : E) (p q : E × ℝ) :
    objective y q - objective x p - inner ℝ (x-p.1) (y-x) =
      q.2-p.2-inner ℝ (x-p.1) (q.1-p.1) + ‖(y-x)-(q.1-p.1)‖^2/2 := by
  have he : y-q.1 = (x-p.1)+((y-x)-(q.1-p.1)) := by abel
  dsimp [objective]
  rw [he, norm_add_sq_real (x-p.1) ((y-x)-(q.1-p.1)), inner_sub_right]
  ring

theorem envelope_lower (P : Epigraph E) (x y : E) :
    envelope P x + inner ℝ (gradient P x) (y-x) ≤ envelope P y := by
  have h := (minimizingPair_supports P x).2 _ (minimizingPair_mem P y)
  change (minimizingPair P x).2 + inner ℝ (gradient P x)
    (proximal P y-proximal P x) ≤ (minimizingPair P y).2 at h
  have he := objective_shift_identity x y (minimizingPair P x) (minimizingPair P y)
  change envelope P y - envelope P x - inner ℝ (gradient P x) (y-x) =
    (minimizingPair P y).2-(minimizingPair P x).2-
      inner ℝ (gradient P x) (proximal P y-proximal P x) +
      ‖(y-x)-(proximal P y-proximal P x)‖^2/2 at he
  nlinarith [sq_nonneg ‖(y-x)-(proximal P y-proximal P x)‖]

theorem envelope_upper (P : Epigraph E) (x y : E) :
    envelope P y ≤ envelope P x + inner ℝ (gradient P x) (y-x) + ‖y-x‖^2/2 := by
  have h := minimizingPair_min P y (minimizingPair P x) (minimizingPair_mem P x)
  have he := objective_shift_identity x y (minimizingPair P x) (minimizingPair P x)
  simp only [sub_self, inner_zero_right, sub_zero, zero_sub, zero_add] at he
  change objective y (minimizingPair P x) - envelope P x -
    inner ℝ (gradient P x) (y-x) = ‖y-x‖^2/2 at he
  linarith

theorem envelope_hasGradientAt (P : Epigraph E) (x : E) :
    HasGradientAt (envelope P) (gradient P x) x := by
  rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hl := envelope_lower P x y
  have hu := envelope_upper P x y
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  nlinarith [norm_nonneg (y-x)]

theorem envelope_convex (P : Epigraph E) : ConvexOn ℝ univ (envelope P) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (envelope_lower P z x) ha
  have hy := mul_le_mul_of_nonneg_left (envelope_lower P z y) hb
  have hi : a * inner ℝ (gradient P z) (x-z) + b * inner ℝ (gradient P z) (y-z) = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have he : a • (x-z) + b • (y-z) = 0 := by
      rw [smul_sub, smul_sub]
      have hz : a • x + b • y = z := rfl
      calc
        a • x - a • z + (b • y-b • z) = (a • x+b • y)-(a+b) • z := by module
        _ = 0 := by rw [hz,hab,one_smul,sub_self]
    rw [he, inner_zero_right]
  change envelope P z ≤ a * envelope P x + b * envelope P y
  have habz : (a+b)*envelope P z = envelope P z := by rw [hab,one_mul]
  nlinarith

theorem supports_monotone (P : Epigraph E) {z w g h : E} {t s : ℝ}
    (hz : Supports P z t g) (hw : Supports P w s h) :
    0 ≤ inner ℝ (g-h) (z-w) := by
  have h1 := hz.2 _ hw.1
  have h2 := hw.2 _ hz.1
  simp only [inner_sub_left, inner_sub_right] at *
  linarith

theorem gradient_lipschitz (P : Epigraph E) (x y : E) :
    ‖gradient P x-gradient P y‖ ≤ ‖x-y‖ := by
  have hm := supports_monotone P (minimizingPair_supports P x) (minimizingPair_supports P y)
  have he : x-y = (proximal P x-proximal P y)+(gradient P x-gradient P y) := by
    dsimp [gradient]; abel
  have hi : ‖gradient P x-gradient P y‖^2 ≤ inner ℝ (gradient P x-gradient P y) (x-y) := by
    rw [he, inner_add_right, real_inner_self_eq_norm_sq]
    linarith
  have hc := real_inner_le_norm (gradient P x-gradient P y) (x-y)
  nlinarith [norm_nonneg (gradient P x-gradient P y), norm_nonneg (x-y)]

theorem proximal_lipschitz (P : Epigraph E) (x y : E) :
    ‖proximal P x-proximal P y‖ ≤ ‖x-y‖ := by
  have hm := supports_monotone P (minimizingPair_supports P x) (minimizingPair_supports P y)
  have he : x-y = (proximal P x-proximal P y)+(gradient P x-gradient P y) := by
    dsimp [gradient]; abel
  have hi : ‖proximal P x-proximal P y‖^2 ≤ inner ℝ (x-y) (proximal P x-proximal P y) := by
    rw [he, inner_add_left, real_inner_self_eq_norm_sq]
    linarith
  have hc := real_inner_le_norm (x-y) (proximal P x-proximal P y)
  nlinarith [norm_nonneg (proximal P x-proximal P y), norm_nonneg (x-y)]

theorem envelope_interpolates (P : Epigraph E) (z g : E) (t : ℝ)
    (h : Supports P z t g) :
    gradient P (z+g) = g ∧ envelope P (z+g) = t+‖g‖^2/2 := by
  have he : (z+g)-z = g := by abel
  have hm := minimizingPair_eq_of_supports P (z+g) z t (he.symm ▸ h)
  simp [gradient, proximal, envelope, hm, objective, he]

end
end StrongSilver.Moreau
