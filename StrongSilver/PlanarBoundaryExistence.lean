-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarAsymptotics

namespace StrongSilver
open Real Set Filter
noncomputable section

/-- The smallness condition is discharged uniformly for 0 ≤ μA ≤ 1.
This proves the bounded boundary ODE used in Lemma 3.3; the invariant domain
and the complete trajectory attachment remain separate geometric steps. -/
theorem eventually_planar_boundary_ode : ∀ᶠ A : ℝ in atTop,
    ∀ μ : ℝ, 0 ≤ μ → μ*A ≤ 1 →
      ∃ J : ℝ → ℝ, J (planarTerminalAngle A) = 0 ∧
        ∀ θ ∈ Icc (0 : ℝ) (planarTerminalAngle A),
          0 ≤ J θ ∧ J θ ≤ 32*A^((9 : ℝ)/20) ∧
          HasDerivWithinAt J
            (planarRiccati μ (explicitArcRadius (planarTerminalAngle A) (planarTerminalRadius A) (planarSlopeScale A) θ)
              (smoothPlanarSlope (planarSlopeScale A) θ) (smoothPlanarSlopeDeriv (planarSlopeScale A) θ) (J θ))
            (Icc (0 : ℝ) (planarTerminalAngle A)) θ := by
  filter_upwards [planar_parameters_eventually] with A hAparams
  obtain ⟨hA,hlog,hεk,hsmall⟩ := hAparams
  intro μ hμ hμA
  have hApos : 0 < A := zero_lt_one.trans hA
  have hε : 0 < planarEpsilon A := Real.rpow_pos_of_pos hApos _
  have hlogpos := Real.log_pos hA
  have hk : 0 < planarSlopeScale A := div_pos (by norm_num) hlogpos
  have hk1 : planarSlopeScale A ≤ 1/2 := by
    apply (div_le_iff₀ hlogpos).mpr
    linarith
  have hR : 1 ≤ planarTerminalRadius A := by
    have hs := Real.sq_sqrt (show 0 ≤ 1+(planarEpsilon A)^2 by positivity)
    have hn := Real.sqrt_nonneg (1+(planarEpsilon A)^2)
    unfold planarTerminalRadius
    nlinarith only [hs,hn,sq_nonneg (planarEpsilon A)]
  obtain ⟨J,hJ0,hJ⟩ := exists_smooth_planar_Riccati hμ hε hk hk1 hεk rfl hR (hsmall μ hμ hμA)
  have hM := planarComparisonBound_power_bound hA hlog
  dsimp only [planarTerminalAngle] at hM
  refine ⟨J,hJ0,fun θ ht => ⟨(hJ θ ht).1,?_,(hJ θ ht).2.2⟩⟩
  have hh := (hJ θ ht).2.1
  linarith

end
end StrongSilver
