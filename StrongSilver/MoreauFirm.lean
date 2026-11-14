-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.MoreauSmooth

namespace StrongSilver.Moreau
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

theorem gradient_firm (P : Epigraph V) (x y : V) :
    ‖gradient P x-gradient P y‖^2 ≤ inner ℝ (gradient P x-gradient P y) (x-y) := by
  have hm := supports_monotone P (minimizingPair_supports P x) (minimizingPair_supports P y)
  have he : x-y = (proximal P x-proximal P y)+(gradient P x-gradient P y) := by unfold gradient; abel
  rw [he,inner_add_right,real_inner_self_eq_norm_sq]
  linarith only [hm]

theorem proximal_firm (P : Epigraph V) (x y : V) :
    ‖proximal P x-proximal P y‖^2 ≤ inner ℝ (proximal P x-proximal P y) (x-y) := by
  have hm := supports_monotone P (minimizingPair_supports P x) (minimizingPair_supports P y)
  have he : x-y = (proximal P x-proximal P y)+(gradient P x-gradient P y) := by unfold gradient; abel
  rw [he,inner_add_right,real_inner_self_eq_norm_sq,
    real_inner_comm (gradient P x-gradient P y) (proximal P x-proximal P y)]
  linarith only [hm]

end
end StrongSilver.Moreau
