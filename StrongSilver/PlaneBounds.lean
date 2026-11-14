-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteInterpolation

namespace StrongSilver.Moreau
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem planeMaximum_increment (rows : List (V × ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hrows : ∀ r ∈ rows, ‖r.1‖ ≤ M) (x y : V) :
    planeMaximum rows x ≤ planeMaximum rows y+M*‖x-y‖ := by
  apply (planeMaximum_le _ _ _).mpr
  refine ⟨add_nonneg (planeMaximum_nonnegative _ _) (mul_nonneg hM (norm_nonneg _)),fun r hr => ?_⟩
  have hp := plane_le_maximum rows r hr y
  have hi := real_inner_le_norm r.1 (x-y)
  have hb := mul_le_mul_of_nonneg_right (hrows r hr) (norm_nonneg (x-y))
  rw [inner_sub_right] at hi
  linarith

variable [ProperSpace V]

theorem plane_envelope_linear_upper (rows : List (V × ℝ)) (hc : ∀ r ∈ rows, 0 ≤ r.2)
    {M : ℝ} (hM : 0 ≤ M) (hrows : ∀ r ∈ rows, ‖r.1‖ ≤ M) (x : V) :
    envelope (planeEpigraph rows hc) x ≤ M*‖x‖ := by
  have hm := minimizingPair_min (planeEpigraph rows hc) x (x,planeMaximum rows x)
    (show planeMaximum rows x ≤ planeMaximum rows x from le_rfl)
  change envelope (planeEpigraph rows hc) x ≤ planeMaximum rows x+‖x-x‖^2/2 at hm
  simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_div,add_zero] at hm
  have hp := planeMaximum_increment rows hM hrows x 0
  rw [planeMaximum_zero rows hc,sub_zero,zero_add] at hp
  exact hm.trans hp

theorem plane_envelope_gradient_bound (rows : List (V × ℝ)) (hc : ∀ r ∈ rows, 0 ≤ r.2)
    {M : ℝ} (hM : 0 ≤ M) (hrows : ∀ r ∈ rows, ‖r.1‖ ≤ M) (x : V) :
    ‖gradient (planeEpigraph rows hc) x‖ ≤ M := by
  let P := planeEpigraph rows hc
  let z := proximal P x
  let g := gradient P x
  let d := (minimizingPair P x).2
  have hs := minimizingPair_supports P x
  have hz : planeMaximum rows z ≤ d := hs.1
  have ht := hs.2 (z+g,planeMaximum rows (z+g))
    (show planeMaximum rows (z+g) ≤ planeMaximum rows (z+g) from le_rfl)
  change d+inner ℝ g ((z+g)-z) ≤ planeMaximum rows (z+g) at ht
  rw [add_sub_cancel_left,real_inner_self_eq_norm_sq] at ht
  have hi := planeMaximum_increment rows hM hrows (z+g) z
  rw [add_sub_cancel_left] at hi
  change ‖g‖ ≤ M
  nlinarith [norm_nonneg g]

end
end StrongSilver.Moreau
