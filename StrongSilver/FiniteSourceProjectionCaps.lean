-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.UnitProjectionBound
import Mathlib.Data.Fintype.BigOperators

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
set_option maxHeartbeats 1800000

/-- Any finite retained family has finite directional caps at a nonzero
source. Only the first group in time will need uniform absolute caps. -/
theorem finite_source_projection_caps {ι : Type*} [Fintype ι] (z g : ι → V) {Y : V} (hY : Y ≠ 0) :
    ∃ M G : ℝ, ∀ i,
      |inner ℝ (unitDirection Y) (z i)| ≤ M*‖Y‖ ∧
      |inner ℝ (unitDirection Y) (g i)| ≤ G*‖Y‖ := by
  let M := (∑ i, |inner ℝ (unitDirection Y) (z i)|)/‖Y‖
  let G := (∑ i, |inner ℝ (unitDirection Y) (g i)|)/‖Y‖
  have hn : ‖Y‖ ≠ 0 := norm_ne_zero_iff.mpr hY
  refine ⟨M,G,fun i => ?_⟩
  have hM : M*‖Y‖ = ∑ i, |inner ℝ (unitDirection Y) (z i)| := div_mul_cancel₀ _ hn
  have hG : G*‖Y‖ = ∑ i, |inner ℝ (unitDirection Y) (g i)| := div_mul_cancel₀ _ hn
  rw [hM,hG]
  exact ⟨Finset.single_le_sum (f := fun j => |inner ℝ (unitDirection Y) (z j)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i),
    Finset.single_le_sum (f := fun j => |inner ℝ (unitDirection Y) (g j)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)⟩

end
end StrongSilver
