-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.RadialArcBody

namespace StrongSilver
open Real Set Complex
noncomputable section

theorem bodyOfCompact_norm_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [ProperSpace V] {S : Set V} (hc : IsCompact S) (h0 : (0 : V) ∈ S) {M : ℝ}
    (hbound : ∀ v ∈ S, ‖v‖ ≤ M) : ∀ v ∈ (bodyOfCompact S hc h0).carrier, ‖v‖ ≤ M := by
  have hsub : S ⊆ Metric.closedBall (0 : V) M := by
    intro v hv
    simpa only [Metric.mem_closedBall,dist_zero_right] using hbound v hv
  have hh := closure_minimal (convexHull_min hsub (convex_closedBall (0 : V) M)) Metric.isClosed_closedBall
  intro v hv
  simpa only [Metric.mem_closedBall,dist_zero_right] using hh hv

theorem polarArc_norm {r : ℝ → ℝ} {θ : ℝ} (hr : 0 ≤ r θ) : ‖polarArc r θ‖ = r θ := by
  rw [polarArc,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,polarUnit_norm,mul_one]

theorem smoothArcRadius_antitoneOn {k₀ Θ R : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) (hR : 0 ≤ R) :
    AntitoneOn (arcRadius Θ R (smoothPlanarSlope k₀)) (Icc (0 : ℝ) Θ) := by
  have hd (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Θ) := smoothArcRadius_hasDerivAt (R := R) hk hk1 hΘ hθ
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt)
    (fun θ hθ => (hd θ (interior_subset hθ)).differentiableAt.differentiableWithinAt)
  intro θ hθ
  have ht := interior_subset hθ
  rw [(hd θ ht).deriv]
  have hkpos := (smoothPlanarSlope_bounds hk ht.1 (ht.2.trans_lt hΘ)).1
  have hrpos : 0 ≤ arcRadius Θ R (smoothPlanarSlope k₀) θ := mul_nonneg hR (Real.exp_pos _).le
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkpos.le) hrpos

/-- The radial head attains the largest norm in the constructed convex body. -/
theorem smoothArcBody_norm_max {k₀ Θ R : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ0 : 0 ≤ Θ) (hΘ : Θ < Real.pi/2) (hR : 0 ≤ R) :
    let r := arcRadius Θ R (smoothPlanarSlope k₀)
    let hc : ContinuousOn r (Icc (0 : ℝ) Θ) := fun s hs =>
      (smoothArcRadius_hasDerivAt hk hk1 hΘ hs).continuousAt.continuousWithinAt
    (∀ v ∈ (radialArcBody Θ r hc).carrier, ‖v‖ ≤ r 0) ∧
      ∃ v ∈ (radialArcBody Θ r hc).carrier, ‖v‖ = r 0 := by
  dsimp only
  let r := arcRadius Θ R (smoothPlanarSlope k₀)
  have hrpos (t : ℝ) : 0 ≤ r t := mul_nonneg hR (Real.exp_pos _).le
  have hanti := smoothArcRadius_antitoneOn hk hk1 hΘ hR
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) Θ := ⟨le_rfl,hΘ0⟩
  constructor
  · apply bodyOfCompact_norm_bound
    intro v hv
    rcases mem_insert_iff.mp hv with rfl | hv
    · simpa only [norm_zero] using hrpos 0
    · obtain ⟨t,ht,rfl⟩ := hv
      rw [polarArc_norm (hrpos t)]
      exact hanti hzero ht ht.1
  · refine ⟨polarArc r 0,polarArc_mem_body _ hzero,?_⟩
    exact polarArc_norm (hrpos 0)

end
end StrongSilver
