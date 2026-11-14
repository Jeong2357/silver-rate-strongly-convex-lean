-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.HingeRaySupport
import StrongSilver.ExactProximalValues

namespace StrongSilver.Moreau
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
set_option maxHeartbeats 1000000

theorem ray_data_of_support (P : Epigraph V) (n : V) {s a t d : ℝ}
    (hs : Supports P (s • n) d (a • n)) (hst : s+a = t) :
    proximal P (t • n) = s • n ∧ gradient P (t • n) = a • n := by
  have he : s • n+a • n = t • n := by rw [← add_smul,hst]
  have hm := minimizingPair_eq_from_supports P (s • n) (a • n) d hs
  have hg := (envelope_interpolates P (s • n) (a • n) d hs).1
  rw [he] at hm hg
  exact ⟨congrArg Prod.fst hm,hg⟩

/-- Exact proximal data on a ray for a common-intercept hinge maximum. -/
theorem hinge_ray_proximal (P : Epigraph V) {n : V} {r Δ t : ℝ}
    (hn : inner ℝ n n = 1) (hr : 0 < r) (hΔ : 0 ≤ Δ) (ht : 0 ≤ t)
    (hplane : ∀ q ∈ P.carrier, inner ℝ (r • n) q.1-Δ ≤ q.2)
    (hray : ∀ s : ℝ, 0 ≤ s → (s • n,max (r*s-Δ) 0) ∈ P.carrier) :
    ∃ s a : ℝ, 0 ≤ s ∧ 0 ≤ a ∧ a ≤ r ∧ s+a = t ∧
      proximal P (t • n) = s • n ∧ gradient P (t • n) = a • n := by
  have hτ : 0 ≤ Δ/r := div_nonneg hΔ hr.le
  have hcancel : r*(Δ/r) = Δ := mul_div_cancel₀ _ hr.ne'
  by_cases hsmall : t ≤ Δ/r
  · have hrt : r*t ≤ Δ := by
      have hm := mul_le_mul_of_nonneg_left hsmall hr.le
      rwa [hcancel] at hm
    have hs := hinge_ray_zero_support P ht hrt hray
    have hs' : Supports P (t • n) 0 ((0 : ℝ) • n) := by simpa only [zero_smul] using hs
    exact ⟨t,0,ht,le_refl 0,hr.le,by ring,ray_data_of_support P n hs' (by ring)⟩
  · by_cases hlarge : Δ/r+r ≤ t
    · have hs0 : 0 ≤ t-r := by linarith
      have hactive : Δ ≤ r*(t-r) := by
        have hm := mul_le_mul_of_nonneg_left hlarge hr.le
        nlinarith only [hm,hcancel]
      have hs := hinge_ray_corner_support P hn hr hs0 hactive hplane hray
      exact ⟨t-r,r,hs0,hr.le,le_refl r,by ring,ray_data_of_support P n hs (by ring)⟩
    · have ha : 0 ≤ t-Δ/r := sub_nonneg.mpr (le_of_not_ge hsmall)
      have har : t-Δ/r ≤ r := by linarith only [le_of_not_ge hlarge]
      have hs := hinge_ray_middle_support P hn hr hΔ ha har hplane hray
      exact ⟨Δ/r,t-Δ/r,hτ,ha,har,by ring,ray_data_of_support P n hs (by ring)⟩

end
end StrongSilver.Moreau
