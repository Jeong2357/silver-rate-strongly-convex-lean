-- SPDX-License-Identifier: GPL-3.0-only
-- The finite-dimensional coordinate transport follows ProblemRealization.lean,
-- silver-rate-lean v1.0.0, Yechan Jeong and Youngjoon Hong.
import StrongSilver.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def Trace.isometry {μ : ℝ} {n : ℕ} (T : Trace V μ n) (U : V →ₗᵢ[ℝ] W) : Trace W μ n where
  x := fun i => U (T.x i)
  z := fun i => U (T.z i)
  g := fun i => U (T.g i)
  d := T.d
  steps := T.steps
  split := by intro i; rw [T.split,map_add]
  nonnegative := T.nonnegative
  origin := by intro i; rw [U.inner_map_map]; exact T.origin i
  supports := by intro i j; rw [← map_sub,U.inner_map_map]; exact T.supports i j
  update := by
    intro i
    simpa only [map_sub,map_smul,map_add] using congrArg U (T.update i)

/-- Compatible traces in any positive finite-dimensional real Hilbert space
provide lower bounds for the exact Euclidean supremum in the problem. -/
theorem Trace.finite_distance_lower [FiniteDimensional ℝ V] {κ μ : ℝ} {n : ℕ}
    (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) (T : Trace V μ n) (hx : T.x 0 ≠ 0) :
    ENNReal.ofReal (‖T.x (Fin.last n)‖^2/‖T.x 0‖^2) ≤ D κ (List.ofFn T.steps) := by
  have hd : 0 < Module.finrank ℝ V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨T.x 0,hx⟩
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have hm' : Module.finrank ℝ V = m+1 := hm
  let U : V ≃ₗᵢ[ℝ] Space m := by
    unfold Space
    rw [← hm']
    exact (stdOrthonormalBasis ℝ V).repr
  let Q := T.isometry U.toLinearIsometry
  have hQ0 : Q.x 0 ≠ 0 := by
    change U (T.x 0) ≠ 0
    intro he
    exact hx (U.injective (by simpa only [map_zero] using he))
  have hb := Q.distance_lower hκ hμ hμ1 hQ0
  change ENNReal.ofReal (‖U (T.x (Fin.last n))‖^2/‖U (T.x 0)‖^2) ≤ D κ (List.ofFn T.steps) at hb
  simpa only [U.norm_map] using hb

end
end StrongSilver
