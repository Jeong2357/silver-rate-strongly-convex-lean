-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.StrongMoreau
import StrongSilver.ConcaveExtrapolation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue

namespace StrongSilver
open Set Real Filter
noncomputable section
set_option maxHeartbeats 1000000

/-- A monotone half-Lipschitz scalar envelope gradient, normalized at zero. -/
structure ScalarContraction where
  g : ℝ → ℝ
  zero : g 0 = 0
  increments : ∀ x y : ℝ, x ≤ y → 0 ≤ g y-g x ∧ g y-g x ≤ (y-x)/2

namespace ScalarContraction
variable (S : ScalarContraction)

theorem monotone : Monotone S.g := fun x y hxy => sub_nonneg.mp (S.increments x y hxy).1

theorem lipschitz : LipschitzWith (1/2) S.g := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.dist_eq]
  change |S.g x-S.g y| ≤ (1/2 : ℝ)*|x-y|
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (S.monotone hxy)),abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith only [(S.increments x y hxy).2]
  · rw [abs_of_nonneg (sub_nonneg.mpr (S.monotone hyx)),abs_of_nonneg (sub_nonneg.mpr hyx)]
    linarith only [(S.increments y x hyx).2]

def proximalMap (x : ℝ) : ℝ := x-S.g x

theorem proximal_continuous : Continuous S.proximalMap := continuous_id.sub S.lipschitz.continuous

theorem proximal_strictMono : StrictMono S.proximalMap := by
  intro x y hxy
  have hh := (S.increments x y hxy.le).2
  change x-S.g x < y-S.g y
  linarith

theorem proximal_zero : S.proximalMap 0 = 0 := by simp only [proximalMap,S.zero,sub_self]

theorem proximal_positive_bounds {x : ℝ} (hx : 0 ≤ x) : x/2 ≤ S.proximalMap x ∧ S.proximalMap x ≤ x := by
  have hh := S.increments 0 x hx
  rw [S.zero] at hh
  dsimp [proximalMap]
  constructor <;> linarith only [hh.1,hh.2]

theorem proximal_negative_upper {x : ℝ} (hx : x ≤ 0) : S.proximalMap x ≤ x/2 := by
  have hh := (S.increments x 0 hx).2
  rw [S.zero] at hh
  dsimp [proximalMap]
  linarith

theorem proximal_surjective : Function.Surjective S.proximalMap := by
  intro y
  let R : ℝ := 2*|y|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hl := S.proximal_negative_upper (neg_nonpos.mpr hR.le)
  have hu := (S.proximal_positive_bounds hR.le).1
  have hy : y ∈ Icc (S.proximalMap (-R)) (S.proximalMap R) := by
    dsimp [R] at hl hu
    constructor <;> linarith [le_abs_self y,neg_abs_le y]
  obtain ⟨x,hx,hxy⟩ := intermediate_value_Icc (by linarith : -R ≤ R) S.proximal_continuous.continuousOn hy
  exact ⟨x,hxy⟩

def proximalIso : ℝ ≃o ℝ :=
  S.proximal_strictMono.orderIsoOfSurjective S.proximalMap S.proximal_surjective

def inverseSlope (z : ℝ) : ℝ := S.g (S.proximalIso.symm z)
def potential (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, S.inverseSlope t

theorem inverseSlope_continuous : Continuous S.inverseSlope :=
  S.lipschitz.continuous.comp S.proximalIso.symm.continuous

theorem inverseSlope_monotone : Monotone S.inverseSlope := S.monotone.comp S.proximalIso.symm.monotone

theorem inverseSlope_proximal (x : ℝ) : S.inverseSlope (S.proximalMap x) = S.g x := by
  change S.g (S.proximalIso.symm (S.proximalIso x)) = S.g x
  rw [OrderIso.symm_apply_apply]

theorem inverseSlope_zero : S.inverseSlope 0 = 0 := by
  have hh := S.inverseSlope_proximal 0
  rwa [S.proximal_zero,S.zero] at hh

theorem potential_hasDerivAt (z : ℝ) : HasDerivAt S.potential (S.inverseSlope z) z :=
  intervalIntegral.integral_hasDerivAt_right (S.inverseSlope_continuous.intervalIntegrable _ _)
    S.inverseSlope_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter S.inverseSlope_continuous.continuousAt

theorem potential_convex : ConvexOn ℝ univ S.potential := by
  apply Monotone.convexOn_univ_of_deriv (fun z => (S.potential_hasDerivAt z).differentiableAt)
  have he : deriv S.potential = S.inverseSlope := funext (fun z => (S.potential_hasDerivAt z).deriv)
  rw [he]
  exact S.inverseSlope_monotone

theorem potential_support (z t : ℝ) : S.potential z+S.inverseSlope z*(t-z) ≤ S.potential t := by
  have hc : ConcaveOn ℝ (Icc (min z t) (max z t)) (fun x => -S.potential x) :=
    S.potential_convex.neg.subset (subset_univ _) (convex_Icc _ _)
  have hh := concave_tangent_upper (d := fun x => -S.inverseSlope x) hc
    (fun x hx => (S.potential_hasDerivAt x).neg.hasDerivWithinAt)
    (show z ∈ Icc (min z t) (max z t) from ⟨min_le_left _ _,le_max_left _ _⟩)
    (show t ∈ Icc (min z t) (max z t) from ⟨min_le_right _ _,le_max_right _ _⟩)
  dsimp [tangentLine] at hh
  linarith only [hh]

theorem potential_zero : S.potential 0 = 0 := intervalIntegral.integral_same

theorem potential_nonnegative (z : ℝ) : 0 ≤ S.potential z := by
  have hh := S.potential_support 0 z
  simpa only [S.potential_zero,S.inverseSlope_zero,zero_mul,add_zero] using hh

def epigraph : Moreau.Epigraph ℝ := Moreau.finiteEpigraph S.potential
  (continuous_iff_continuousAt.mpr (fun z => (S.potential_hasDerivAt z).continuousAt))
    S.potential_convex S.potential_nonnegative S.potential_zero

theorem supports_proximal (x : ℝ) : Moreau.Supports S.epigraph (S.proximalMap x)
    (S.potential (S.proximalMap x)) (S.g x) := by
  refine ⟨(show S.potential (S.proximalMap x) ≤ S.potential (S.proximalMap x) from le_rfl),fun q hq => ?_⟩
  have hh := S.potential_support (S.proximalMap x) q.1
  rw [S.inverseSlope_proximal] at hh
  change S.potential (S.proximalMap x)+inner ℝ (S.g x) (q.1-S.proximalMap x) ≤ q.2
  rw [Real.inner_apply]
  exact hh.trans hq

/-- Reconstruct an actual convex potential, with the prescribed gradient at every real point. -/
theorem envelope_gradient (x : ℝ) : Moreau.gradient S.epigraph x = S.g x := by
  have hh := (Moreau.envelope_interpolates S.epigraph (S.proximalMap x) (S.g x)
    (S.potential (S.proximalMap x)) (S.supports_proximal x)).1
  have he : S.proximalMap x+S.g x = x := by dsimp [proximalMap]; ring
  rwa [he] at hh

end ScalarContraction
end
end StrongSilver
