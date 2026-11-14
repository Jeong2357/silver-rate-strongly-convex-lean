-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PolyhedralCone
import StrongSilver.SubgraphDomain

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000

def wedgeUpper (c s : ℝ) : ℂ := ⟨c,s⟩
def wedgeLower (c s : ℝ) : ℂ := ⟨c,-s⟩
def wedgeInward (c s : ℝ) (i : Fin 2) : ℂ := if i = 0 then ⟨s,-c⟩ else ⟨s,c⟩
def wedgeForm (c s : ℝ) (i : Fin 2) : ℂ →L[ℝ] ℝ := innerSL ℝ (wedgeInward c s i)
def wedgeCone (c s : ℝ) : Set ℂ := linearCone (wedgeForm c s)

theorem wedge_mem_iff (c s : ℝ) (x : ℂ) : x ∈ wedgeCone c s ↔
    0 ≤ s*x.re-c*x.im ∧ 0 ≤ s*x.re+c*x.im := by
  constructor
  · intro hx
    have h0 := hx (0 : Fin 2)
    have h1 := hx (1 : Fin 2)
    change 0 ≤ inner ℝ (wedgeInward c s 0) x at h0
    change 0 ≤ inner ℝ (wedgeInward c s 1) x at h1
    simp only [wedgeInward,ite_true,complex_inner_coordinates,neg_mul] at h0
    norm_num [wedgeInward,if_false,complex_inner_coordinates] at h1
    exact ⟨by linarith only [h0],by nlinarith only [h1]⟩
  · intro hx i
    fin_cases i
    · change 0 ≤ inner ℝ (wedgeInward c s 0) x
      simp only [wedgeInward,ite_true,complex_inner_coordinates,neg_mul]
      linarith only [hx.1]
    · change 0 ≤ inner ℝ (wedgeInward c s 1) x
      norm_num [wedgeInward,if_false,complex_inner_coordinates]
      nlinarith only [hx.2]

theorem wedge_re_nonnegative {c s : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ∈ wedgeCone c s) : 0 ≤ x.re := by
  have hh := (wedge_mem_iff c s x).mp hx
  by_contra hneg
  have hm := mul_neg_of_pos_of_neg hs (lt_of_not_ge hneg)
  nlinarith only [hh.1,hh.2,hm]

theorem wedge_upper_projection_nonnegative {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c)
    {x : ℂ} (hx : x ∈ wedgeCone c s) : 0 ≤ inner ℝ (wedgeUpper c s) x := by
  have hh := (wedge_mem_iff c s x).mp hx
  have hX := wedge_re_nonnegative hs hx
  have hd : 0 ≤ c^2-s^2 := by nlinarith only [hc,hs,hsc]
  have hdX := mul_nonneg hd hX
  have hsface := mul_nonneg hs.le hh.2
  rw [wedgeUpper,complex_inner_coordinates]
  by_contra hn
  have hp := mul_neg_of_pos_of_neg hc (lt_of_not_ge hn)
  nlinarith only [hdX,hsface,hp]

theorem wedge_lower_projection_nonnegative {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c)
    {x : ℂ} (hx : x ∈ wedgeCone c s) : 0 ≤ inner ℝ (wedgeLower c s) x := by
  have hh := (wedge_mem_iff c s x).mp hx
  have hX := wedge_re_nonnegative hs hx
  have hd : 0 ≤ c^2-s^2 := by nlinarith only [hc,hs,hsc]
  have hdX := mul_nonneg hd hX
  have hsface := mul_nonneg hs.le hh.1
  rw [wedgeLower,complex_inner_coordinates,neg_mul]
  by_contra hn
  have hp := mul_neg_of_pos_of_neg hc (lt_of_not_ge hn)
  nlinarith only [hdX,hsface,hp]

theorem wedge_frame_upper {c s : ℝ} (hu : c^2+s^2 = 1) (x : ℂ) :
    x-inner ℝ (wedgeUpper c s) x • wedgeUpper c s =
      (inner ℝ (wedgeInward c s 0) x) • wedgeInward c s 0 := by
  apply Complex.ext <;> simp only [Complex.sub_re,Complex.sub_im,Complex.smul_re,Complex.smul_im,
    wedgeUpper,wedgeInward,ite_true,complex_inner_coordinates,smul_eq_mul]
  · nlinarith only [congrArg (fun t : ℝ => t*x.re) hu]
  · nlinarith only [congrArg (fun t : ℝ => t*x.im) hu]

theorem wedge_frame_lower {c s : ℝ} (hu : c^2+s^2 = 1) (x : ℂ) :
    x-inner ℝ (wedgeLower c s) x • wedgeLower c s =
      (inner ℝ (wedgeInward c s 1) x) • wedgeInward c s 1 := by
  apply Complex.ext <;> norm_num [Complex.sub_re,Complex.sub_im,Complex.smul_re,Complex.smul_im,
    wedgeLower,wedgeInward,if_false,complex_inner_coordinates,smul_eq_mul]
  · nlinarith only [congrArg (fun t : ℝ => t*x.re) hu]
  · nlinarith only [congrArg (fun t : ℝ => t*x.im) hu]

end
end StrongSilver
