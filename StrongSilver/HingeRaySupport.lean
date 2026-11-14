-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.MoreauSmooth

namespace StrongSilver.Moreau
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
set_option maxHeartbeats 1000000

theorem zero_support_of_zero_height (P : Epigraph V) {z : V} (hz : (z,0) ∈ P.carrier) : Supports P z 0 0 := by
  refine ⟨hz,fun q hq => ?_⟩
  rw [inner_zero_left,add_zero]
  exact P.nonnegative q hq

theorem hinge_ray_corner_support (P : Epigraph V) {n : V} {r Δ s : ℝ}
    (hn : inner ℝ n n = 1) (hr : 0 < r) (hs : 0 ≤ s) (hactive : Δ ≤ r*s)
    (hplane : ∀ q ∈ P.carrier, inner ℝ (r • n) q.1-Δ ≤ q.2)
    (hray : ∀ t : ℝ, 0 ≤ t → (t • n,max (r*t-Δ) 0) ∈ P.carrier) :
    Supports P (s • n) (r*s-Δ) (r • n) := by
  refine ⟨?_,fun q hq => ?_⟩
  · simpa only [max_eq_left (sub_nonneg.mpr hactive)] using hray s hs
  · have hh := hplane q hq
    simp only [real_inner_smul_left] at hh
    simp only [inner_sub_right,real_inner_smul_right,real_inner_smul_left,hn,mul_one]
    nlinarith only [hh]

theorem hinge_ray_zero_support (P : Epigraph V) {n : V} {r Δ s : ℝ} (hs : 0 ≤ s) (hactive : r*s ≤ Δ)
    (hray : ∀ t : ℝ, 0 ≤ t → (t • n,max (r*t-Δ) 0) ∈ P.carrier) : Supports P (s • n) 0 0 := by
  apply zero_support_of_zero_height
  simpa only [max_eq_right (sub_nonpos.mpr hactive)] using hray s hs

theorem hinge_ray_middle_support (P : Epigraph V) {n : V} {r Δ a : ℝ}
    (hn : inner ℝ n n = 1) (hr : 0 < r) (hΔ : 0 ≤ Δ) (ha : 0 ≤ a) (har : a ≤ r)
    (hplane : ∀ q ∈ P.carrier, inner ℝ (r • n) q.1-Δ ≤ q.2)
    (hray : ∀ t : ℝ, 0 ≤ t → (t • n,max (r*t-Δ) 0) ∈ P.carrier) :
    Supports P ((Δ/r) • n) 0 (a • n) := by
  have hcancel : r*(Δ/r) = Δ := mul_div_cancel₀ Δ hr.ne'
  refine ⟨?_,fun q hq => ?_⟩
  · have hh := hray (Δ/r) (div_nonneg hΔ hr.le)
    simpa only [hcancel,sub_self,max_self] using hh
  · have hp := hplane q hq
    have hpa := mul_le_mul_of_nonneg_left hp (div_nonneg ha hr.le)
    have hθ : a/r ≤ 1 := (div_le_one hr).mpr har
    have hupper := mul_le_mul_of_nonneg_right hθ (P.nonnegative q hq)
    have hcancel' : (a/r)*r = a := div_mul_cancel₀ a hr.ne'
    rw [real_inner_smul_left] at hp hpa
    simp only [inner_sub_right,real_inner_smul_left,real_inner_smul_right,hn,mul_one,zero_add]
    have he : (a/r)*(r*inner ℝ n q.1-Δ) = a*inner ℝ n q.1-a*(Δ/r) := by
      field_simp [hr.ne']
      <;> ring
    rw [he] at hpa
    simp only [one_mul] at hupper
    nlinarith only [hpa,hupper]

end
end StrongSilver.Moreau
