-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConePlaneRows
import StrongSilver.PlaneBounds

namespace StrongSilver
open Real Complex
noncomputable section
set_option maxHeartbeats 1000000

theorem coneRay_im_abs {c s : ℝ} (hs : 0 ≤ s) {n : ℂ} (hn : n ∈ coneRays c s) : |n.im| = s := by
  simp only [coneRays,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;>
    simp only [wedgeUpper,wedgeLower,Complex.neg_im,abs_neg,abs_of_nonneg hs]

theorem conePlaneRows_im_bound {a d r c s Δ B : ℝ} (hd : 0 ≤ d) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hdB : d ≤ B) (hrB : r*s ≤ B) : ∀ p ∈ conePlaneRows a d r c s Δ, |p.1.im| ≤ B := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simpa only [abs_neg,abs_of_nonneg hd] using hdB
  · obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hp
    rw [Complex.smul_im,smul_eq_mul,abs_mul,abs_of_nonneg hr,coneRay_im_abs hs hn]
    exact hrB

theorem conePlaneRows_norm_bound {a d r c s Δ B : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (hu : c^2+s^2 = 1) (had : a+d ≤ B) (hrB : r ≤ B) :
    ∀ p ∈ conePlaneRows a d r c s Δ, ‖p.1‖ ≤ B := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · have hn := Complex.norm_le_abs_re_add_abs_im (⟨a,-d⟩ : ℂ)
    have hn' : ‖(⟨a,-d⟩ : ℂ)‖ ≤ a+d := by simpa only [abs_neg,abs_of_nonneg ha,abs_of_nonneg hd] using hn
    exact hn'.trans had
  · obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hp
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,coneRay_norm hu hn,mul_one]
    exact hrB

theorem planeMaximum_axis_zero (rows : List (ℂ × ℝ)) {Δ B Z y : ℝ} (hB : 0 ≤ B)
    (hrows : ∀ p ∈ rows, p.2 = Δ) (hcoeff : ∀ p ∈ rows, |p.1.im| ≤ B)
    (hBZ : B*Z ≤ Δ) (hy : |y| ≤ Z) : Moreau.planeMaximum rows (⟨0,y⟩ : ℂ) = 0 := by
  apply le_antisymm _ (Moreau.planeMaximum_nonnegative _ _)
  apply (Moreau.planeMaximum_le _ _ _).mpr
  refine ⟨le_rfl,fun p hp => ?_⟩
  rw [hrows p hp,complex_inner_coordinates,mul_zero,zero_add]
  have habs := le_abs_self (p.1.im*y)
  rw [abs_mul] at habs
  have hm := mul_le_mul (hcoeff p hp) hy (abs_nonneg y) hB
  nlinarith only [habs,hm,hBZ]

end
end StrongSilver
