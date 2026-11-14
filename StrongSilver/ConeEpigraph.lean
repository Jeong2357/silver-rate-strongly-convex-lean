-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConePlaneRows

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000

def coneEpigraph (a d r c s Δ : ℝ) (hΔ : 0 ≤ Δ) : Moreau.Epigraph ℂ :=
  Moreau.planeEpigraph (conePlaneRows a d r c s Δ)
    (fun p hp => by rw [conePlaneRows_intercept a d r c s Δ p hp]; exact hΔ)

theorem coneEpigraph_ray_data {a d r c s Δ : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hu : c^2+s^2 = 1) (hr : 0 < r) (hΔ : 0 ≤ Δ) (hradius : r = a*c+d*s)
    {n : ℂ} (hn : n ∈ coneRays c s) (t : ℝ) (ht : 0 ≤ t) :
    ∃ p g : ℝ, 0 ≤ p ∧ 0 ≤ g ∧ g ≤ r ∧ p+g = t ∧
      Moreau.proximal (coneEpigraph a d r c s Δ hΔ) (t • n) = p • n ∧
      Moreau.gradient (coneEpigraph a d r c s Δ hΔ) (t • n) = g • n := by
  have hactive : (r • n,Δ) ∈ conePlaneRows a d r c s Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨n,hn,rfl⟩)
  exact Moreau.common_intercept_ray_data (conePlaneRows a d r c s Δ) hΔ hr (coneRay_inner hu hn)
    (conePlaneRows_intercept a d r c s Δ) (conePlaneRows_slope ha hd hc hs hu hr.le hradius hn) hactive t ht

end
end StrongSilver
