-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusCompact

namespace StrongSilver.Scalar.Silver
open Set
noncomputable section
set_option maxHeartbeats 1000000

theorem splitPotential_at_rho : splitPotential rho rho=0 := by
  simpa only [diagonalPotential,splitPotential,two_mul] using diagonalPotential_at_rho

theorem splitPotential_continuousAt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ContinuousAt (fun x : ℝ × ℝ => splitPotential x.1 x.2) (a,b) := by
  have h1 := (scalarPotential_derivative a ha).continuousAt.comp (continuousAt_fst : ContinuousAt Prod.fst (a,b))
  have h2 := (scalarPotential_derivative b hb).continuousAt.comp (continuousAt_snd : ContinuousAt Prod.snd (a,b))
  have hz : 0 < a+b+1 := by linarith
  have hZ : ContinuousAt (fun x : ℝ × ℝ => x.1+x.2+1) (a,b) := by fun_prop
  have h3 := (scalarPotential_derivative (a+b+1) hz).continuousAt.comp (f := fun x : ℝ × ℝ => x.1+x.2+1) (x := (a,b)) hZ
  exact (h1.add h2).sub h3

theorem splitPotential_left_derivative (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x => splitPotential x b) (scalarFirst a-scalarFirst (a+b+1)) a := by
  have hi : HasDerivAt (fun x : ℝ => x+b+1) 1 a := by
    convert! ((hasDerivAt_id a).add_const b).add_const 1 using 1 <;> simp
  convert! ((scalarPotential_derivative a ha).add_const (scalarPotential b)).sub
    ((scalarPotential_derivative _ (by linarith : 0 < a+b+1)).comp a hi) using 1 <;> simp

theorem splitPotential_right_derivative (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x => splitPotential a x) (scalarFirst b-scalarFirst (a+b+1)) b := by
  have hi : HasDerivAt (fun x : ℝ => a+x+1) 1 b := by
    convert! ((hasDerivAt_id b).const_add a).add_const 1 using 1 <;> simp
  convert! ((scalarPotential_derivative b hb).const_add (scalarPotential a)).sub
    ((scalarPotential_derivative _ (by linarith : 0 < a+b+1)).comp b hi) using 1 <;> simp

theorem global_minimum_diagonal (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmin : ∀ x y : ℝ, 0 < x → 0 < y → splitPotential a b ≤ splitPotential x y) : a=b := by
  have hl : IsLocalMin (fun x => splitPotential x b) a := by
    filter_upwards [Ioi_mem_nhds ha] with x hx
    exact hmin x b hx hb
  have hr : IsLocalMin (fun y => splitPotential a y) b := by
    filter_upwards [Ioi_mem_nhds hb] with y hy
    exact hmin a y ha hy
  have h1 := hl.hasDerivAt_eq_zero (splitPotential_left_derivative a b ha hb)
  have h2 := hr.hasDerivAt_eq_zero (splitPotential_right_derivative a b ha hb)
  exact stationary_pair_diagonal a b ha hb (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)

/-- The actual scalar split potential is globally nonnegative. Compactness,
boundary exclusion, the actual partial derivatives, and the diagonal minimum
are all proved inside the project. -/
theorem splitPotential_nonnegative (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 ≤ splitPotential a b := by
  obtain ⟨l,U,hl,hlU,hbarrier⟩ := splitPotential_compact_barrier
  have hr : rho ∈ Icc l U := by
    by_contra hn
    have h := hbarrier rho rho rho_positive rho_positive (Or.inl hn)
    rw [splitPotential_at_rho] at h
    linarith [minimum_positive]
  let K := (Icc l U) ×ˢ (Icc l U)
  have hcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun x : ℝ × ℝ => splitPotential x.1 x.2) K := by
    intro x hx
    exact (splitPotential_continuousAt x.1 x.2 (hl.trans_le hx.1.1) (hl.trans_le hx.2.1)).continuousWithinAt
  obtain ⟨p,hp,hmin⟩ := hcompact.exists_isMinOn ⟨(rho,rho),hr,hr⟩ hcont
  have hp1 : 0 < p.1 := hl.trans_le hp.1.1
  have hp2 : 0 < p.2 := hl.trans_le hp.2.1
  have hpzero : splitPotential p.1 p.2 ≤ 0 := by
    have h := hmin (show (rho,rho) ∈ K from ⟨hr,hr⟩)
    change splitPotential p.1 p.2 ≤ splitPotential rho rho at h
    rw [splitPotential_at_rho] at h
    exact h
  have hglobal : ∀ x y : ℝ, 0 < x → 0 < y → splitPotential p.1 p.2 ≤ splitPotential x y := by
    intro x y hx hy
    by_cases hK : (x,y) ∈ K
    · exact hmin hK
    · have hout : x ∉ Icc l U ∨ y ∉ Icc l U := by
        change ¬(x ∈ Icc l U ∧ y ∈ Icc l U) at hK
        exact not_and_or.mp hK
      have h := hbarrier x y hx hy hout
      linarith [minimum_positive]
  have heq := global_minimum_diagonal p.1 p.2 hp1 hp2 hglobal
  have hdiag := diagonalPotential_nonnegative p.1 hp1
  have hident : splitPotential p.1 p.2=diagonalPotential p.1 := by
    rw [← heq]
    unfold splitPotential diagonalPotential
    rw [show p.1+p.1+1=2*p.1+1 by ring]
    ring
  rw [← hident] at hdiag
  exact hdiag.trans (hglobal a b ha hb)

theorem splitPotential_zero_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    splitPotential a b=0 ↔ a=rho ∧ b=rho := by
  constructor
  · intro hzero
    have hmin : ∀ x y : ℝ, 0 < x → 0 < y → splitPotential a b ≤ splitPotential x y := by
      intro x y hx hy
      rw [hzero]
      exact splitPotential_nonnegative x y hx hy
    have heq := global_minimum_diagonal a b ha hb hmin
    have hident : splitPotential a b=diagonalPotential a := by
      rw [← heq]
      unfold splitPotential diagonalPotential
      rw [show a+a+1=2*a+1 by ring]
      ring
    have hd : diagonalPotential a=0 := hident.symm.trans hzero
    have har : a=rho := by
      by_contra hn
      have hpos := diagonalPotential_positive a ha hn
      linarith
    exact ⟨har,heq ▸ har⟩
  · rintro ⟨rfl,rfl⟩
    exact splitPotential_at_rho

end
end StrongSilver.Scalar.Silver
