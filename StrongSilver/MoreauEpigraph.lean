-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Order.Compact

namespace StrongSilver.Moreau
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A closed convex epigraph of a nonnegative extended-valued potential
which vanishes at the origin. -/
structure Epigraph (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  carrier : Set (E × ℝ)
  closed : IsClosed carrier
  convex : Convex ℝ carrier
  nonnegative : ∀ p ∈ carrier, 0 ≤ p.2
  zero_mem : (0,0) ∈ carrier
  upward : ∀ p ∈ carrier, ∀ s, p.2 ≤ s → (p.1,s) ∈ carrier

def objective (x : E) (p : E × ℝ) : ℝ := p.2 + ‖x-p.1‖^2 / 2

theorem continuous_objective (x : E) : Continuous (objective x) := by
  unfold objective
  fun_prop

theorem objective_nonnegative (P : Epigraph E) (x : E) (p : E × ℝ)
    (hp : p ∈ P.carrier) : 0 ≤ objective x p :=
  add_nonneg (P.nonnegative p hp) (by positivity)

theorem objective_sublevel_bounded (P : Epigraph E) (x : E) (p : E × ℝ)
    (hp : p ∈ P.carrier) (h : objective x p ≤ objective x (0,0)) :
    p ∈ Metric.closedBall 0 (‖x‖^2 + 2*‖x‖ + 1) := by
  have ht := P.nonnegative p hp
  have hb : p.2 + ‖x-p.1‖^2/2 ≤ ‖x‖^2/2 := by simpa [objective] using h
  have hd : ‖x-p.1‖ ≤ ‖x‖ := by nlinarith [norm_nonneg (x-p.1), norm_nonneg x]
  have hx : ‖p.1‖ ≤ 2*‖x‖ := by
    have he : p.1 = x - (x-p.1) := by abel
    calc
      ‖p.1‖ = ‖x-(x-p.1)‖ := congrArg norm he
      _ ≤ ‖x‖ + ‖x-p.1‖ := norm_sub_le _ _
      _ ≤ 2*‖x‖ := by linarith
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  constructor
  · nlinarith [sq_nonneg ‖x‖]
  · rw [Real.norm_eq_abs, abs_of_nonneg ht]
    nlinarith [sq_nonneg ‖x-p.1‖, norm_nonneg x, sq_nonneg ‖x‖]

theorem exists_minimizer [ProperSpace E] (P : Epigraph E) (x : E) :
    ∃ p ∈ P.carrier, ∀ q ∈ P.carrier, objective x p ≤ objective x q := by
  let R := ‖x‖^2 + 2*‖x‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hc : IsCompact (P.carrier ∩ Metric.closedBall (0 : E × ℝ) R) :=
    (isCompact_closedBall _ _).inter_left P.closed
  have hz : (0,0) ∈ P.carrier ∩ Metric.closedBall (0 : E × ℝ) R :=
    ⟨P.zero_mem, by simpa using hR⟩
  obtain ⟨p,hp,hm⟩ := hc.exists_isMinOn ⟨_,hz⟩ (continuous_objective x).continuousOn
  refine ⟨p,hp.1,fun q hq => ?_⟩
  by_cases hb : objective x q ≤ objective x (0,0)
  · exact hm ⟨hq,objective_sublevel_bounded P x q hq hb⟩
  · exact (hm hz).trans (le_of_not_ge hb)

/-- Supporting inequality for the proximal point, without differentiating the potential. -/
def Supports (P : Epigraph E) (z : E) (t : ℝ) (g : E) : Prop :=
  (z,t) ∈ P.carrier ∧ ∀ q ∈ P.carrier, t + inner ℝ g (q.1-z) ≤ q.2

theorem objective_expansion (x z w : E) (t s α : ℝ) :
    objective x ((1-α) • (z,t) + α • (w,s)) - objective x (z,t) =
      α * (s-t-inner ℝ (x-z) (w-z)) + α^2 * ‖w-z‖^2/2 := by
  have he : x-((1-α) • z + α • w) = (x-z)-α • (w-z) := by module
  change ((1-α)*t+α*s) + ‖x-((1-α) • z+α • w)‖^2/2 -
    (t+‖x-z‖^2/2) = _
  rw [he, norm_sub_sq_real (x-z) (α • (w-z)), real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem minimizer_supports (P : Epigraph E) (x : E) (p : E × ℝ)
    (hp : p ∈ P.carrier) (hm : ∀ q ∈ P.carrier, objective x p ≤ objective x q) :
    Supports P p.1 p.2 (x-p.1) := by
  refine ⟨hp,fun q hq => ?_⟩
  have hα (α : ℝ) (hpos : 0 < α) (hle : α ≤ 1) :
      0 ≤ q.2-p.2-inner ℝ (x-p.1) (q.1-p.1) + α*‖q.1-p.1‖^2/2 := by
    have hc := P.convex hp hq (sub_nonneg.mpr hle) hpos.le (by ring : 1-α+α=1)
    have hd := sub_nonneg.mpr (hm _ hc)
    rw [objective_expansion x p.1 q.1 p.2 q.2 α] at hd
    have he : α * (q.2-p.2-inner ℝ (x-p.1) (q.1-p.1) + α*‖q.1-p.1‖^2/2) =
      α * (q.2-p.2-inner ℝ (x-p.1) (q.1-p.1)) + α^2*‖q.1-p.1‖^2/2 := by ring
    rw [← he] at hd
    exact nonneg_of_mul_nonneg_right hd hpos
  by_contra hn
  have he : 0 < p.2+inner ℝ (x-p.1) (q.1-p.1)-q.2 := by linarith
  let α := min 1 ((p.2+inner ℝ (x-p.1) (q.1-p.1)-q.2) / (‖q.1-p.1‖^2+1))
  have ha : 0 < α := lt_min zero_lt_one (div_pos he (by positivity))
  have hb : α*(‖q.1-p.1‖^2+1) ≤ p.2+inner ℝ (x-p.1) (q.1-p.1)-q.2 := by
    exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hh := hα α ha (min_le_left _ _)
  nlinarith [sq_nonneg ‖q.1-p.1‖]

theorem supports_strong_minimum (P : Epigraph E) (x z : E) (t : ℝ)
    (h : Supports P z t (x-z)) (q : E × ℝ) (hq : q ∈ P.carrier) :
    objective x (z,t) + ‖q.1-z‖^2/2 ≤ objective x q := by
  have hs := h.2 q hq
  have he : x-q.1 = (x-z)-(q.1-z) := by abel
  dsimp [objective]
  rw [he, norm_sub_sq_real (x-z) (q.1-z)]
  linarith

theorem supports_minimizer (P : Epigraph E) (x z : E) (t : ℝ)
    (h : Supports P z t (x-z)) (q : E × ℝ) (hq : q ∈ P.carrier) :
    objective x (z,t) ≤ objective x q := by
  have hh := supports_strong_minimum P x z t h q hq
  nlinarith [sq_nonneg ‖q.1-z‖]

theorem minimizer_unique (P : Epigraph E) (x : E) (p q : E × ℝ)
    (hp : p ∈ P.carrier) (hq : q ∈ P.carrier)
    (hpm : ∀ r ∈ P.carrier, objective x p ≤ objective x r)
    (hqm : ∀ r ∈ P.carrier, objective x q ≤ objective x r) : p = q := by
  have hs := supports_strong_minimum P x p.1 p.2 (minimizer_supports P x p hp hpm) q hq
  have hm := hqm p hp
  have hn : ‖q.1-p.1‖ = 0 := by nlinarith [sq_nonneg ‖q.1-p.1‖, norm_nonneg (q.1-p.1)]
  have he : q.1 = p.1 := sub_eq_zero.mp (norm_eq_zero.mp hn)
  apply Prod.ext he.symm
  have hm' := hpm q hq
  dsimp [objective] at hm hm'
  rw [he] at hm hm'
  linarith

end
end StrongSilver.Moreau
