-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.HingeRayProx

namespace StrongSilver.Moreau
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
set_option maxHeartbeats 1000000

theorem common_intercept_ray_data (rows : List (V × ℝ)) {Δ r : ℝ} {n : V}
    (hΔ : 0 ≤ Δ) (hr : 0 < r) (hn : inner ℝ n n = 1)
    (hrows : ∀ p ∈ rows, p.2 = Δ) (hslope : ∀ p ∈ rows, inner ℝ p.1 n ≤ r)
    (hactive : (r • n,Δ) ∈ rows) (t : ℝ) (ht : 0 ≤ t) :
    let hc : ∀ p ∈ rows, 0 ≤ p.2 := fun p hp => by rw [hrows p hp]; exact hΔ
    ∃ s a : ℝ, 0 ≤ s ∧ 0 ≤ a ∧ a ≤ r ∧ s+a = t ∧
      proximal (planeEpigraph rows hc) (t • n) = s • n ∧
      gradient (planeEpigraph rows hc) (t • n) = a • n := by
  dsimp only
  apply hinge_ray_proximal _ hn hr hΔ ht
  · intro q hq
    have hh := (plane_le_maximum rows (r • n,Δ) hactive q.1).trans hq
    exact hh
  · intro s hs
    change planeMaximum rows (s • n) ≤ max (r*s-Δ) 0
    apply (planeMaximum_le _ _ _).mpr
    refine ⟨le_max_right _ _,fun p hp => ?_⟩
    rw [hrows p hp,real_inner_smul_right]
    have hm := mul_le_mul_of_nonneg_left (hslope p hp) hs
    exact (by nlinarith only [hm] : s*inner ℝ p.1 n-Δ ≤ r*s-Δ).trans (le_max_left _ _)

end
end StrongSilver.Moreau
