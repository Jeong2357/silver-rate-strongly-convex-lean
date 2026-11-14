-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Real

/-!
Exact target of Theorem 1.1 in Sharp_Silver_Bound_Strongly_Convex.pdf.
The proposition `MainLowerBound` below is proved by
`StrongSilver.silver_rate_lower_bound` in `StrongSilver/Main.lean`.
The objective class and both suprema contain actual functions and GD iterates.
-/
namespace StrongSilver
noncomputable section

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

def iterate {E : Type*} [AddCommGroup E] [Module ℝ E]
    (h : List ℝ) (g : E → E) (x : E) : E :=
  h.foldl (fun y a => y - a • g y) x

structure Admissible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (κ : ℝ) (f : E → ℝ) (g : E → E) : Prop where
  strong_convex : StrongConvexOn Set.univ (1 / κ) f
  gradient : ∀ x, HasGradientAt f (g x) x
  smooth : ∀ x y, ‖g x - g y‖ ≤ ‖x - y‖

/-- One actual objective, starting point and minimizer in positive finite dimension. -/
structure Instance (κ : ℝ) where
  dimension : ℕ
  f : Space dimension → ℝ
  g : Space dimension → Space dimension
  admissible : Admissible κ f g
  start : Space dimension
  minimizer : Space dimension
  minimal : ∀ x, f minimizer ≤ f x
  distinct : start ≠ minimizer

def distanceError (h : List ℝ) {κ : ℝ} (w : Instance κ) : ℝ :=
  ‖iterate h w.g w.start - w.minimizer‖ ^ 2 / ‖w.start - w.minimizer‖ ^ 2

def valueError (h : List ℝ) {κ : ℝ} (w : Instance κ) : ℝ :=
  (w.f (iterate h w.g w.start) - w.f w.minimizer) /
    (w.f w.start - w.f w.minimizer)

def D (κ : ℝ) (h : List ℝ) : ENNReal :=
  ⨆ w : Instance κ, ENNReal.ofReal (distanceError h w)

def E (κ : ℝ) (h : List ℝ) : ENNReal :=
  ⨆ w : Instance κ, ENNReal.ofReal (valueError h w)

def rho : ℝ := 1 + Real.sqrt 2
def p : ℝ := Real.log rho / Real.log 2
def nu : ℝ := 1 / p

/-- One pair of absolute constants, before κ, the horizon, and the real schedule. -/
def MainLowerBound : Prop :=
  ∃ C κ₀ : ℝ, 0 < C ∧ 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ ≤ κ → ∀ h : List ℝ,
    ENNReal.ofReal (Real.exp (-C * (h.length : ℝ) * κ ^ (-nu))) ≤ D κ h ∧
    ENNReal.ofReal (Real.exp (-C * (h.length : ℝ) * κ ^ (-nu))) ≤ E κ h

end
end StrongSilver
