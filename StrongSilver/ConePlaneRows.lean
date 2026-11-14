-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WedgeGeometry
import StrongSilver.PlaneHingeRays

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000

def coneRays (c s : ℝ) : List ℂ := [wedgeUpper c s,wedgeLower c s,-wedgeUpper c s,-wedgeLower c s]
def conePlaneRows (a d r c s Δ : ℝ) : List (ℂ × ℝ) :=
  ((⟨a,-d⟩ : ℂ),Δ)::((coneRays c s).map (fun n => (r • n,Δ)))

theorem wedgeUpper_inner {c s : ℝ} (hu : c^2+s^2 = 1) : inner ℝ (wedgeUpper c s) (wedgeUpper c s) = 1 := by
  rw [wedgeUpper,complex_inner_coordinates]
  nlinarith only [hu]

theorem wedgeLower_inner {c s : ℝ} (hu : c^2+s^2 = 1) : inner ℝ (wedgeLower c s) (wedgeLower c s) = 1 := by
  rw [wedgeLower,complex_inner_coordinates]
  nlinarith only [hu]

theorem coneRay_inner {c s : ℝ} (hu : c^2+s^2 = 1) {n : ℂ} (hn : n ∈ coneRays c s) : inner ℝ n n = 1 := by
  simp only [coneRays,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact wedgeUpper_inner hu
  · exact wedgeLower_inner hu
  · rw [inner_neg_left,inner_neg_right,neg_neg]; exact wedgeUpper_inner hu
  · rw [inner_neg_left,inner_neg_right,neg_neg]; exact wedgeLower_inner hu

theorem coneRay_norm {c s : ℝ} (hu : c^2+s^2 = 1) {n : ℂ} (hn : n ∈ coneRays c s) : ‖n‖ = 1 := by
  have hh := coneRay_inner hu hn
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith only [hh,norm_nonneg n]

theorem connecting_slope_ray_upper {a d c s : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hc : 0 ≤ c) (hs : 0 ≤ s)
    {n : ℂ} (hn : n ∈ coneRays c s) : inner ℝ (⟨a,-d⟩ : ℂ) n ≤ a*c+d*s := by
  simp only [coneRays,List.mem_cons,List.not_mem_nil,or_false] at hn
  have hac := mul_nonneg ha hc
  have hds := mul_nonneg hd hs
  rcases hn with rfl | rfl | rfl | rfl <;>
    simp only [wedgeUpper,wedgeLower,complex_inner_coordinates,Complex.neg_re,Complex.neg_im]
  all_goals nlinarith only [hac,hds]

theorem conePlaneRows_intercept (a d r c s Δ : ℝ) : ∀ p ∈ conePlaneRows a d r c s Δ, p.2 = Δ := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact rfl
  · obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hp
    exact rfl

theorem conePlaneRows_slope {a d r c s Δ : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hu : c^2+s^2 = 1) (hr : 0 ≤ r) (hradius : r = a*c+d*s) {n : ℂ} (hn : n ∈ coneRays c s) :
    ∀ p ∈ conePlaneRows a d r c s Δ, inner ℝ p.1 n ≤ r := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · rw [hradius]
    exact connecting_slope_ray_upper ha hd hc hs hn
  · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hp
    rw [real_inner_smul_left]
    have hi := real_inner_le_norm m n
    rw [coneRay_norm hu hm,coneRay_norm hu hn,one_mul] at hi
    exact (mul_le_mul_of_nonneg_left hi hr).trans_eq (mul_one r)

end
end StrongSilver
