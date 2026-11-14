-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarCurveMonotonicity
import StrongSilver.PlanarHeadBounds

namespace StrongSilver
open Real Set Filter Complex
noncomputable section

def planarRadius (A : ℝ) : ℝ → ℝ :=
  explicitArcRadius (planarTerminalAngle A) (planarTerminalRadius A) (planarSlopeScale A)
def planarSlope (A : ℝ) : ℝ → ℝ := smoothPlanarSlope (planarSlopeScale A)
def planarSlopeDerivative (A : ℝ) : ℝ → ℝ := smoothPlanarSlopeDeriv (planarSlopeScale A)

/-- Data proved to exist below, rather than assumptions for the final lower bound. -/
structure PlanarBoundaryCertificate (A μ : ℝ) where
  large : 1 < A
  log_large : 1600 ≤ Real.log A
  epsilon_slope : planarEpsilon A ≤ planarSlopeScale A
  mu_nonnegative : 0 ≤ μ
  mu_size : μ*A ≤ 1
  J : ℝ → ℝ
  terminal : J (planarTerminalAngle A) = 0
  nonnegative : ∀ θ ∈ Icc (0 : ℝ) (planarTerminalAngle A), 0 ≤ J θ
  bound : ∀ θ ∈ Icc (0 : ℝ) (planarTerminalAngle A), J θ ≤ 32*A^((9 : ℝ)/20)
  derivative : ∀ θ ∈ Icc (0 : ℝ) (planarTerminalAngle A),
    HasDerivWithinAt J (planarRiccati μ (planarRadius A θ) (planarSlope A θ) (planarSlopeDerivative A θ) (J θ))
      (Icc (0 : ℝ) (planarTerminalAngle A)) θ

theorem eventually_exists_planar_boundary_certificate : ∀ᶠ A : ℝ in atTop,
    ∀ μ : ℝ, 0 ≤ μ → μ*A ≤ 1 → Nonempty (PlanarBoundaryCertificate A μ) := by
  filter_upwards [planar_parameters_eventually,eventually_planar_boundary_ode] with A hp hode
  intro μ hμ hμA
  obtain ⟨J,hJ0,hJ⟩ := hode μ hμ hμA
  exact ⟨{
    large := hp.1
    log_large := hp.2.1
    epsilon_slope := hp.2.2.1
    mu_nonnegative := hμ
    mu_size := hμA
    J := J
    terminal := hJ0
    nonnegative := fun θ ht => (hJ θ ht).1
    bound := fun θ ht => (hJ θ ht).2.1
    derivative := fun θ ht => (hJ θ ht).2.2
  }⟩

namespace PlanarBoundaryCertificate
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C
set_option maxHeartbeats 800000

theorem epsilon_pos : 0 < planarEpsilon A := Real.rpow_pos_of_pos (zero_lt_one.trans C.large) _
theorem scale_pos : 0 < planarSlopeScale A := div_pos (by norm_num) (Real.log_pos C.large)
theorem scale_le : planarSlopeScale A ≤ 1/16 := (div_le_iff₀ (Real.log_pos C.large)).mpr (by linarith [C.log_large])
theorem angle_pos : 0 < planarTerminalAngle A := Real.arctan_pos.mpr (inv_pos.mpr C.epsilon_pos)
theorem angle_lt : planarTerminalAngle A < Real.pi/2 := Real.arctan_lt_pi_div_two _
theorem mu_lt_one : μ < 1 := by
  have hh := (le_div_iff₀ (zero_lt_one.trans C.large)).mpr C.mu_size
  exact hh.trans_lt ((div_lt_one (zero_lt_one.trans C.large)).mpr C.large)

theorem denominator_pos {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
    0 < Real.cos θ+2*planarSlopeScale A*Real.sin θ :=
  lt_of_lt_of_le (by linarith [C.scale_pos] : 0 < 2*planarSlopeScale A)
    (smoothPlanar_denominator_lower C.scale_pos (by linarith [C.scale_le]) ⟨ht.1,ht.2.trans C.angle_lt.le⟩)

theorem slope_pos {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) : 0 < planarSlope A θ :=
  (smoothPlanarSlope_bounds C.scale_pos ht.1 (ht.2.trans_lt C.angle_lt)).1

theorem radius_pos (θ : ℝ) : 0 < planarRadius A θ :=
  mul_pos (Real.sqrt_pos.2 (by positivity : 0 < 1+(planarEpsilon A)^2)) (Real.exp_pos _)

theorem radius_hasDerivAt {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
    HasDerivAt (planarRadius A) (-planarSlope A θ*planarRadius A θ) θ :=
  explicitArcRadius_hasDerivAt (C.denominator_pos ht).ne'

theorem slope_hasDerivAt {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
    HasDerivAt (planarSlope A) (planarSlopeDerivative A θ) θ :=
  smoothPlanarSlope_hasDerivAt (C.denominator_pos ht).ne'

def curve : ℝ → ℂ := planarBoundaryCurve (planarRadius A) (planarSlope A) C.J
def field : ℝ → ℂ := planarBoundaryField μ (planarRadius A) (planarSlope A) C.J

theorem field_coordinates {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
    0 < (C.field θ).re ∧ 0 ≤ (C.field θ).im := by
  apply planarBoundaryField_coordinates C.mu_nonnegative (C.radius_pos θ) (C.slope_pos ht)
    (C.nonnegative θ ht) ht.1 (ht.2.trans_lt C.angle_lt)
  exact (smoothPlanarSlope_bounds C.scale_pos ht.1 (ht.2.trans_lt C.angle_lt)).2.2

theorem curve_hasDerivWithinAt {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
    ∃ t : ℝ, t < 0 ∧ HasDerivWithinAt C.curve (t • C.field θ) (Icc (0 : ℝ) (planarTerminalAngle A)) θ := by
  have hkp := (smoothPlanarSlopeDeriv_bounds C.scale_pos (by linarith [C.scale_le]) ⟨ht.1,ht.2.trans C.angle_lt.le⟩).1
  change -(1 : ℝ)/2 ≤ planarSlopeDerivative A θ at hkp
  exact planarBoundaryCurve_hasDerivWithinAt_field (C.radius_hasDerivAt ht).hasDerivWithinAt
    (C.slope_hasDerivAt ht).hasDerivWithinAt (C.derivative θ ht) C.mu_nonnegative (C.radius_pos θ)
    (C.slope_pos ht) (by linarith) (C.nonnegative θ ht)

theorem x_strictAnti : StrictAntiOn (fun θ => (C.curve θ).re) (Icc (0 : ℝ) (planarTerminalAngle A)) :=
  (planar_curve_coordinates_antitone (fun θ ht => C.curve_hasDerivWithinAt ht) (fun θ ht => C.field_coordinates ht)).1

theorem y_antitone : AntitoneOn (fun θ => (C.curve θ).im) (Icc (0 : ℝ) (planarTerminalAngle A)) :=
  (planar_curve_coordinates_antitone (fun θ ht => C.curve_hasDerivWithinAt ht) (fun θ ht => C.field_coordinates ht)).2

theorem curve_continuousOn : ContinuousOn C.curve (Icc (0 : ℝ) (planarTerminalAngle A)) := by
  intro θ ht
  obtain ⟨t,htn,hd⟩ := C.curve_hasDerivWithinAt ht
  exact hd.continuousWithinAt

theorem radius_continuousOn : ContinuousOn (planarRadius A) (Icc (0 : ℝ) (planarTerminalAngle A)) :=
  fun θ ht => (C.radius_hasDerivAt ht).continuousAt.continuousWithinAt

def body : CompactConvexBody ℂ := radialArcBody (planarTerminalAngle A) (planarRadius A) C.radius_continuousOn

theorem arc_support {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
    ∀ s ∈ Icc (0 : ℝ) (planarTerminalAngle A),
      inner ℝ (polarNormal (planarSlope A θ) θ) (polarArc (planarRadius A) s) ≤
        inner ℝ (polarNormal (planarSlope A θ) θ) (polarArc (planarRadius A) θ) := by
  intro s hs
  apply polarArc_support (fun t ht => C.radius_hasDerivAt ht) (fun t ht => (C.radius_pos t).le)
    (smoothNormalAngle_strictMonoOn C.scale_pos (by linarith [C.scale_le]) C.angle_lt).monotoneOn
    (fun t ht => ⟨(smoothNormalAngle_first_quadrant C.scale_pos ht.1 (ht.2.trans_lt C.angle_lt)).1,
      (smoothNormalAngle_first_quadrant C.scale_pos ht.1 (ht.2.trans_lt C.angle_lt)).2.le⟩) ht hs

theorem field_is_actual_gradient {θ : ℝ} (ht : θ ∈ Icc (0 : ℝ) (planarTerminalAngle A)) :
    stronglyConvexGradient μ (Moreau.gradient C.body.supportEpigraph) (C.curve θ) = C.field θ :=
  planarBoundaryField_is_gradient C.radius_continuousOn ht (C.radius_pos θ).le (C.slope_pos ht)
    (C.nonnegative θ ht) (C.arc_support ht)

theorem curve_terminal : C.curve (planarTerminalAngle A) = (⟨planarEpsilon A,1⟩ : ℂ) := by
  unfold curve
  rw [planarBoundaryCurve_terminal C.terminal]
  change explicitArcRadius (planarTerminalAngle A) (planarTerminalRadius A) (planarSlopeScale A) (planarTerminalAngle A) •
    polarUnit (planarTerminalAngle A) = _
  simp only [explicitArcRadius,sub_self,Real.exp_zero,mul_one]
  exact terminal_polar_vector C.epsilon_pos

theorem head_y_ge_one : 1 ≤ C.J 0 := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (planarTerminalAngle A) := ⟨le_rfl,C.angle_pos.le⟩
  have hend : planarTerminalAngle A ∈ Icc (0 : ℝ) (planarTerminalAngle A) := ⟨C.angle_pos.le,le_rfl⟩
  have hh := C.y_antitone hzero hend C.angle_pos.le
  change (C.curve (planarTerminalAngle A)).im ≤ (C.curve 0).im at hh
  rw [C.curve_terminal] at hh
  simpa only [curve,planarBoundaryCurve_head] using hh

end PlanarBoundaryCertificate
end
end StrongSilver
