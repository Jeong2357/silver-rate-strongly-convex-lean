-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeEpigraph
import StrongSilver.ConeSlopeBounds
import StrongSilver.SignedWedgeNormal
import StrongSilver.PairedConePredecessor
import StrongSilver.BackwardPathInSet
import StrongSilver.BackwardNormAnyPath
import StrongSilver.MoreauAtZero

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1600000

theorem cone_epigraph_backward_path {a d r c s Δ μ : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c) (hu : c^2+s^2 = 1)
    (hr : 0 < r) (hradius : r = a*c+d*s) (hΔ : 0 ≤ Δ) (hda : d ≤ a) (hra : r ≤ 2*a)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (h : List ℝ) (hcritical : ∀ b ∈ h, 1-μ*b ≠ 0)
    (y : ℂ) (hy : y ∈ wedgeCone c s ∪ oppositeSet (wedgeCone c s)) (hy0 : y ≠ 0) :
    let P := coneEpigraph a d r c s Δ hΔ
    ∃ x : ℂ, iterate h (stronglyConvexGradient μ (Moreau.gradient P)) x = y ∧
      (∀ i : ℕ, i ≤ h.length → iterate (h.take i) (stronglyConvexGradient μ (Moreau.gradient P)) x ∈
        wedgeCone c s ∪ oppositeSet (wedgeCone c s)) ∧
      ‖x‖ ≤ Real.exp (inverseCharge μ h)*(‖y‖+(1-μ)*(2*a)*smallPositiveSum μ h) ∧
      (∀ i : ℕ, iterate (h.take i) (stronglyConvexGradient μ (Moreau.gradient P)) x ≠ 0) := by
  dsimp only
  let P := coneEpigraph a d r c s Δ hΔ
  let F := stronglyConvexObjective μ (Moreau.envelope P)
  let G := stronglyConvexGradient μ (Moreau.gradient P)
  have hrows := conePlaneRows_norm_bound (Δ := Δ) ha.le hd hr.le hu (by linarith : a+d ≤ 2*a) hra
  have hgrad := strongify_gradient (μ := μ) (Moreau.envelope_hasGradientAt P)
  have henv (x : ℂ) : Moreau.envelope P x ≤ (2*a)*‖x‖ :=
    Moreau.plane_envelope_linear_upper _ _ (by linarith : 0 ≤ 2*a) hrows x
  have hlower (x : ℂ) : (μ/2)*‖x‖^2 ≤ F x := by
    have hh := mul_nonneg (sub_nonneg.mpr hμ1) (Moreau.envelope_nonnegative P x)
    dsimp [F,stronglyConvexObjective]
    linarith only [hh]
  have hupper (x : ℂ) : F x ≤ (μ/2)*‖x‖^2+((1-μ)*(2*a))*‖x‖ := by
    have hh := mul_le_mul_of_nonneg_left (henv x) (sub_nonneg.mpr hμ1)
    dsimp [F,stronglyConvexObjective]
    nlinarith only [hh]
  have hrad : WedgeRayRadial P c s := by
    intro n hn t ht
    obtain ⟨p,g,hp,hg,hgr,hpg,hprox,hgrad⟩ := coneEpigraph_ray_data ha.le hd hc.le hs.le hu hr hΔ hradius hn t ht
    exact ⟨p,g,hprox,hgrad⟩
  have horth : ∀ x ∈ wedgeCone c s, ∀ q, OutwardNormal (wedgeCone c s) x q → inner ℝ q (G x) = 0 :=
    fun x hx q hq => wedge_physical_normal_orthogonal P μ hc hs hsc hu hrad hx hq
  have hopp : ∀ x ∈ oppositeSet (wedgeCone c s), ∀ q,
      OutwardNormal (oppositeSet (wedgeCone c s)) x q → inner ℝ q (G x) = 0 :=
    fun x hx q hq => wedge_opposite_physical_normal_orthogonal P μ hc hs hsc hu hrad hx hq
  have hcone : ∀ x ∈ wedgeCone c s, ∀ t : ℝ, 0 ≤ t → t • x ∈ wedgeCone c s :=
    fun x hx t ht => linearCone_smul (wedgeForm c s) hx ht
  obtain ⟨x,hx,hrun,hstates⟩ := exists_backward_path_in_set h G (wedgeCone c s ∪ oppositeSet (wedgeCone c s))
    (fun b hb y hy => paired_cone_predecessor hμ (linearCone_closed _) (linearCone_convex _) hcone F G hgrad hlower hupper
      horth hopp (hcritical b hb) hy) hy
  have hgbound (z : ℂ) : ‖Moreau.gradient P z‖ ≤ 2*a :=
    Moreau.plane_envelope_gradient_bound _ _ (by linarith : 0 ≤ 2*a) hrows z
  have hnorm := backward_norm_of_iterate hμ hμ1 (by linarith : 0 ≤ 2*a) (Moreau.gradient P)
    (Moreau.gradient_inner_nonnegative P) hgbound h hcritical x y hrun
  have hG0 : G 0 = 0 := by
    dsimp [G,stronglyConvexGradient]
    simp only [Moreau.gradient_at_zero P,smul_zero,add_zero,mul_zero]
  exact ⟨x,hrun,hstates,hnorm,fun i => iterate_prefix_ne_zero hG0 hrun hy0 i⟩

end
end StrongSilver
