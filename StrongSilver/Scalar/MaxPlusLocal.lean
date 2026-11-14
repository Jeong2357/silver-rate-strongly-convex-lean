-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusHessian
import StrongSilver.Scalar.SecondOrderLower

namespace StrongSilver.Scalar.Silver
open Set
noncomputable section
set_option maxHeartbeats 800000

def splitPotential (a b : ℝ) : ℝ := scalarPotential a+scalarPotential b-scalarPotential (a+b+1)

theorem hessian_near : ∃ δ > 0, δ ≤ rho/2 ∧
    ∀ a b : ℝ, |a-rho| < δ → |b-rho| < δ → ∀ u v : ℝ,
      (hessianMargin/2)*(u^2+v^2) ≤
        scalarSecond a*u^2+scalarSecond b*v^2-scalarSecond (a+b+1)*(u+v)^2 := by
  have heps : 0 < hessianMargin/6 := by linarith [hessianMargin_positive]
  obtain ⟨d₁,hd₁,h₁⟩ := Metric.continuousAt_iff.mp (scalarSecond_continuousAt rho rho_positive) _ heps
  obtain ⟨d₂,hd₂,h₂⟩ := Metric.continuousAt_iff.mp (scalarSecond_continuousAt (rho^2) (sq_pos_of_pos rho_positive)) _ heps
  let δ := min (rho/2) (min d₁ (d₂/2))
  have hδ : 0 < δ := lt_min (by linarith [rho_positive]) (lt_min hd₁ (by linarith))
  have hδ₁ : δ ≤ d₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₂ : 2*δ ≤ d₂ := by have h := (min_le_right (rho/2) (min d₁ (d₂/2))).trans (min_le_right d₁ (d₂/2)); linarith
  refine ⟨δ,hδ,min_le_left _ _,fun a b ha hb u v => hessian_stability _ _ _ u v ?_ ?_ ?_⟩
  · have h := h₁ (show dist a rho < d₁ by simpa only [Real.dist_eq] using ha.trans_le hδ₁)
    exact le_of_lt (by simpa only [Real.dist_eq] using h)
  · have h := h₁ (show dist b rho < d₁ by simpa only [Real.dist_eq] using hb.trans_le hδ₁)
    exact le_of_lt (by simpa only [Real.dist_eq] using h)
  · have hdist : dist (a+b+1) (rho^2) < d₂ := by
      rw [Real.dist_eq,rho_square]
      have he : a+b+1-(2*rho+1)=(a-rho)+(b-rho) := by ring
      rw [he]
      have h := abs_add_le (a-rho) (b-rho)
      linarith
    have h := h₂ hdist
    exact le_of_lt (by simpa only [Real.dist_eq] using h)

def splitLine (u v t : ℝ) : ℝ := splitPotential (rho+t*u) (rho+t*v)
def splitLineFirst (u v t : ℝ) : ℝ :=
  u*scalarFirst (rho+t*u)+v*scalarFirst (rho+t*v)-(u+v)*scalarFirst ((rho+t*u)+(rho+t*v)+1)
def splitLineSecond (u v t : ℝ) : ℝ :=
  u^2*scalarSecond (rho+t*u)+v^2*scalarSecond (rho+t*v)-(u+v)^2*scalarSecond ((rho+t*u)+(rho+t*v)+1)

theorem splitLine_derivative (u v t : ℝ) (ha : 0 < rho+t*u) (hb : 0 < rho+t*v) :
    HasDerivAt (splitLine u v) (splitLineFirst u v t) t := by
  have hA : HasDerivAt (fun s : ℝ => rho+s*u) u t := by convert! ((hasDerivAt_id t).mul_const u).const_add rho using 1 <;> simp
  have hB : HasDerivAt (fun s : ℝ => rho+s*v) v t := by convert! ((hasDerivAt_id t).mul_const v).const_add rho using 1 <;> simp
  have h := ((scalarPotential_derivative _ ha).comp t hA).add ((scalarPotential_derivative _ hb).comp t hB)
  have h' := h.sub ((scalarPotential_derivative _ (by linarith : 0 < (rho+t*u)+(rho+t*v)+1)).comp t ((hA.add hB).add_const 1))
  convert! h' using 1 <;> try rfl
  unfold splitLineFirst
  ring

theorem splitLineFirst_derivative (u v t : ℝ) (ha : 0 < rho+t*u) (hb : 0 < rho+t*v) :
    HasDerivAt (splitLineFirst u v) (splitLineSecond u v t) t := by
  have hA : HasDerivAt (fun s : ℝ => rho+s*u) u t := by convert! ((hasDerivAt_id t).mul_const u).const_add rho using 1 <;> simp
  have hB : HasDerivAt (fun s : ℝ => rho+s*v) v t := by convert! ((hasDerivAt_id t).mul_const v).const_add rho using 1 <;> simp
  have h := (((scalarFirst_derivative _ ha).comp t hA).const_mul u).add (((scalarFirst_derivative _ hb).comp t hB).const_mul v)
  have h' := h.sub (((scalarFirst_derivative _ (by linarith : 0 < (rho+t*u)+(rho+t*v)+1)).comp t ((hA.add hB).add_const 1)).const_mul (u+v))
  convert! h' using 1 <;> try rfl
  unfold splitLineSecond
  ring

theorem splitLine_zero (u v : ℝ) : splitLine u v 0=0 := by
  have h := diagonalPotential_at_rho
  simpa only [splitLine,splitPotential,diagonalPotential,zero_mul,add_zero,two_mul] using h

theorem splitLineFirst_zero (u v : ℝ) : splitLineFirst u v 0=0 := by
  unfold splitLineFirst
  simp only [zero_mul,add_zero,show rho+rho+1=rho^2 by rw [rho_square]; ring]
  rw [← scalarFirst_at_rho]
  ring

/-- The positive-definite Hessian gives an actual uniform quadratic lower
bound on a neighborhood; both derivatives along the segment are proved. -/
theorem splitPotential_local_lower : ∃ δ > 0, ∀ a b : ℝ, |a-rho| < δ → |b-rho| < δ →
    (hessianMargin/4)*((a-rho)^2+(b-rho)^2) ≤ splitPotential a b := by
  obtain ⟨δ,hδ,hδrho,hH⟩ := hessian_near
  refine ⟨δ,hδ,fun a b ha hb => ?_⟩
  let u := a-rho
  let v := b-rho
  have hclose (w t : ℝ) (hw : |w| < δ) (ht : t ∈ Icc (0 : ℝ) 1) : |(rho+t*w)-rho| < δ := by
    have htt : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have h := mul_le_mul_of_nonneg_right htt (abs_nonneg w)
    rw [add_sub_cancel_left,abs_mul]
    linarith
  have hpos (w t : ℝ) (hw : |w| < δ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < rho+t*w := by
    have hc := hclose w t hw ht
    have hh := (abs_lt.mp hc).1
    linarith [rho_positive]
  have hbound := Calculus.second_order_lower (splitLine u v) (splitLineFirst u v) (splitLineSecond u v)
    ((hessianMargin/2)*(u^2+v^2)) (splitLine_zero u v) (splitLineFirst_zero u v)
    (fun t ht => splitLine_derivative u v t (hpos u t ha ht) (hpos v t hb ht))
    (fun t ht => splitLineFirst_derivative u v t (hpos u t ha ht) (hpos v t hb ht))
    (fun t ht => by
      have h := hH (rho+t*u) (rho+t*v) (hclose u t ha ht) (hclose v t hb ht) u v
      simpa only [splitLineSecond,mul_comm] using h)
  have hline : splitLine u v 1=splitPotential a b := by simp [splitLine,u,v]
  rw [hline] at hbound
  dsimp [u,v] at hbound
  nlinarith

end
end StrongSilver.Scalar.Silver
