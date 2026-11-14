-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseReference
import StrongSilver.DifferentiableBoxBound

namespace StrongSilver.SilverBalance
noncomputable section
set_option maxHeartbeats 2400000

abbrev Parameters := Fin 9 → ℝ

def center : Parameters := fun _ => 1

def leftSum (u : Parameters) : ℝ := rho*u 0+rho*u 1+u 4
def rightSum (u : Parameters) : ℝ := rho*u 2+rho*u 3+u 6

/-- The normalized masses and excesses determined by three consecutive
balanced splits. Parameters are the nine local ratios at the three vertices. -/
def shape (u : Parameters) : FourPhase.Shape :=
  ![1,u 1/u 0,(u 8/u 7)*(leftSum u/rightSum u)*(u 2/u 0),
    (u 8/u 7)*(leftSum u/rightSum u)*(u 3/u 0),u 4/(rho*u 0),
    u 5*leftSum u/(rho^2*u 0*u 7),
    (u 8/u 7)*(leftSum u/rightSum u)*u 6/(rho*u 0),0]

@[simp] theorem leftSum_center : leftSum center = rho^2 := by
  unfold leftSum center
  nlinarith only [rho_square]

@[simp] theorem rightSum_center : rightSum center = rho^2 := by
  unfold rightSum center
  nlinarith only [rho_square]

@[simp] theorem shape_center : shape center = FourPhase.reference := by
  have hr := rho_positive.ne'
  ext i
  fin_cases i
  all_goals simp [shape,center,FourPhase.reference,hr]

theorem differentiableAt_coordinate (i : Fin 8) :
    DifferentiableAt ℝ (fun u => shape u i) center := by
  have hr : rho ≠ 0 := rho_positive.ne'
  have h0 : center 0 ≠ 0 := by norm_num [center]
  have h7 : center 7 ≠ 0 := by norm_num [center]
  have hR : rightSum center ≠ 0 := by simp only [rightSum_center]; exact pow_ne_zero _ hr
  fin_cases i
  all_goals simp only [shape,Matrix.cons_val_zero',Matrix.cons_val_succ',div_eq_mul_inv]
  all_goals unfold leftSum rightSum at *
  all_goals fun_prop (disch := aesop)

/-- Three balanced splits give a linearly small perturbation of the
silver four-gap reference shape, with absolute constants. -/
theorem exists_shape_box : ∃ C > 0, ∃ δ > 0, ∀ ε : ℝ,
    0 ≤ ε → ε ≤ δ → ∀ u : Parameters,
    (∀ i, |u i-1| ≤ ε) → ∀ j, |shape u j-FourPhase.reference j| ≤ C*ε := by
  have hb (j : Fin 8) := differentiable_box_bound (differentiableAt_coordinate j)
  choose C hC δ hδ hbound using hb
  let c := Finset.univ.sup' Finset.univ_nonempty C
  let d := Finset.univ.inf' Finset.univ_nonempty δ
  have hcle (j : Fin 8) : C j ≤ c := Finset.le_sup' C (Finset.mem_univ j)
  have hdle (j : Fin 8) : d ≤ δ j := Finset.inf'_le δ (Finset.mem_univ j)
  have hc : 0 < c := (hC 0).trans_le (hcle 0)
  have hd : 0 < d := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => hδ j)
  refine ⟨c,hc,d,hd,fun ε hε hεδ u hu j => ?_⟩
  have h := hbound j ε hε (hεδ.trans (hdle j)) u hu
  rw [show shape center j = FourPhase.reference j by rw [shape_center]] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hcle j) hε)

end
end StrongSilver.SilverBalance
