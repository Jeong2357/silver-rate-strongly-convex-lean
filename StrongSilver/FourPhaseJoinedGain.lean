-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseGeometricFactory
import StrongSilver.FourPhaseLocalJoiningScale
import StrongSilver.FourPhaseAttachedRatio

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2800000

/-- The normalized logarithmic gain including the last joining scale.
The absolute constants precede all schedules and all normalized data. -/
theorem exists_joined_gain_constants : ∃ C > 0, ∃ δ > 0,
    ∀ D : LocalParameters, ∀ J : D.JoiningScaleConditions, ∀ ε : ℝ,
    0 ≤ ε → ε ≤ δ →
    (∀ i : Fin 8, i ≠ 7 → |D.shape i-reference i| ≤ ε) → D.ζ ≤ δ →
    gain D.shape+(gain D.shape+gainLeft D.shape+gainRight D.shape)/Real.sqrt 2-
      C*ε*(|gain D.shape|+|gainLeft D.shape|+|gainRight D.shape|)-C*D.ζ ≤
    Real.log ((D.joiningScale/lastExcess D.μ D.T D.gap D.pivot)^2*
      (totalMass D.shape^2/‖source D.shape‖^2)) := by
  obtain ⟨C₀,hC₀,δ,hδ,hgeom⟩ := exists_four_phase_geometry
  let C := C₀+24
  refine ⟨C,by dsimp [C]; linarith only [hC₀],δ,hδ,fun D J ε hε hεδ hx hζδ => ?_⟩
  have hζ0 : 0 ≤ D.shape 7 := D.offset_nonnegative
  have hζδ' : D.shape 7 ≤ δ := hζδ
  have hlocal := (hgeom ε hε hεδ D.shape hx hζ0 hζδ').2.2.2
  have hK := D.joiningScale_bounds J
  have hk : 0 < lastExcess D.μ D.T D.gap D.pivot := by linarith only [J.last_excess_lower]
  have hnorm : 0 < totalMass D.shape^2/‖source D.shape‖^2 :=
    div_pos (sq_pos_of_pos D.geometry.regular.totalMass_positive)
      (sq_pos_of_pos (norm_pos_iff.mpr (source_nonzero D.geometry.regular)))
  rw [Real.log_mul (pow_ne_zero _ (div_pos hK.1 hk).ne') hnorm.ne',Real.log_pow]
  have hS : 0 ≤ |gain D.shape|+|gainLeft D.shape|+|gainRight D.shape| := by positivity
  have hp := mul_nonneg hε hS
  have hz : D.shape 7 = D.ζ := rfl
  rw [hz] at hlocal
  dsimp only [C]
  nlinarith only [hlocal,hK.2.2.2,hp]

/-- Rewriting the dimensionless gain as the actual squared source norm
ratio after aligning the new endpoint with the retained source. -/
theorem attached_log_gain_identity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : LocalParameters) (J : D.JoiningScaleConditions) {Y : V} (hY : Y ≠ 0) :
    Real.log ((‖Y‖^2/‖axisAttachment Y D.joiningScale (source D.shape)‖^2)*
      (totalMass D.shape/lastExcess D.μ D.T D.gap D.pivot)^2) =
    Real.log ((D.joiningScale/lastExcess D.μ D.T D.gap D.pivot)^2*
      (totalMass D.shape^2/‖source D.shape‖^2)) := by
  have hX : source D.shape ≠ 0 := source_nonzero D.geometry.regular
  rw [attached_source_ratio hY (D.joiningScale_bounds J).1.ne' hX]
  congr 1
  have hk : lastExcess D.μ D.T D.gap D.pivot ≠ 0 := by
    have hh := J.last_excess_lower; linarith only [hh]
  have hn := norm_ne_zero_iff.mpr hX
  field_simp
  <;> ring

end
end StrongSilver.FourPhase
