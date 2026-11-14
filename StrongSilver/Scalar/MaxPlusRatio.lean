-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusPotential

namespace StrongSilver.Scalar.Silver
open Set
noncomputable section
set_option maxHeartbeats 800000

def powerSecant (y : ℝ) : ℝ := (y^(1-nu)-1)/(y-1)
def diagonalRatio (x : ℝ) : ℝ :=
  nu*((2*x+1)*x^nu/x-(2*x+1)^nu)/(1+1/x)

theorem powerSecant_positive (y : ℝ) (hy : 1 < y) : 0 < powerSecant y := by
  apply div_pos _ (by linarith)
  have h := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) hy (by linarith [nu_lt_one] : 0 < 1-nu)
  rw [Real.one_rpow] at h
  linarith

theorem powerSecant_strictAnti : StrictAntiOn powerSecant (Ioi 1) := by
  intro x hx y hy hxy
  change 1 < x at hx
  change 1 < y at hy
  have hc := Real.strictConcaveOn_rpow (by linarith [nu_lt_one] : 0 < 1-nu) (by linarith [nu_positive] : 1-nu < 1)
  have h := hc.secant_strict_mono (a := 1) (by norm_num) (by change 0 ≤ x; linarith)
    (by change 0 ≤ y; linarith) (by linarith : x ≠ 1) (by linarith : y ≠ 1) hxy
  simpa only [Real.one_rpow,powerSecant] using h

theorem rescaled_power_identity (u x : ℝ) (hu : 0 < u) (hx : 0 < x) :
    u^nu*(u/x)^(1-nu)=u*x^nu/x := by
  rw [Real.div_rpow hu.le hx.le,Real.rpow_sub hu,Real.rpow_sub hx,Real.rpow_one,Real.rpow_one]
  have hp : u^nu ≠ 0 := (Real.rpow_pos_of_pos hu nu).ne'
  have hq : x^nu ≠ 0 := (Real.rpow_pos_of_pos hx nu).ne'
  field_simp <;> ring

theorem diagonalRatio_secant (x : ℝ) (hx : 0 < x) :
    diagonalRatio x=nu*(2*x+1)^nu*powerSecant (2+1/x) := by
  have he : 2+1/x=(2*x+1)/x := by field_simp <;> ring
  have hid := rescaled_power_identity (2*x+1) x (by linarith) hx
  rw [← he] at hid
  unfold diagonalRatio powerSecant
  have hden : (2+1/x)-1=1+1/x := by ring
  rw [hden]
  have hnum : nu*((2*x+1)*x^nu/x-(2*x+1)^nu)=
      nu*(2*x+1)^nu*((2+1/x)^(1-nu)-1) := by linear_combination -nu*hid
  rw [hnum]
  ring

theorem diagonalRatio_strictMono : StrictMonoOn diagonalRatio (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  rw [diagonalRatio_secant x hx,diagonalRatio_secant y hy]
  have hbase : 0 < 2*x+1 := by linarith
  have hpower : (2*x+1)^nu < (2*y+1)^nu :=
    Real.rpow_lt_rpow hbase.le (by linarith) nu_positive
  have hxarg : 1 < 2+1/x := by have := one_div_pos.mpr hx; linarith
  have hyarg : 1 < 2+1/y := by have := one_div_pos.mpr hy; linarith
  have harg : 2+1/y < 2+1/x := by
    have h := one_div_lt_one_div_of_lt hx hxy
    linarith
  have hs := powerSecant_strictAnti hyarg hxarg harg
  have hp := powerSecant_positive (2+1/x) hxarg
  have hq := Real.rpow_pos_of_pos (by linarith : 0 < 2*y+1) nu
  have hprod := mul_lt_mul hpower hs.le hp hq.le
  simpa only [mul_assoc] using mul_lt_mul_of_pos_left hprod nu_positive

theorem diagonalRatio_at_rho : diagonalRatio rho=coefficient := by
  have hu : 2*rho+1=rho^2 := rho_square.symm
  unfold diagonalRatio coefficient
  rw [hu,rho_rpow_nu,rho_square_rpow_nu]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hr : rho ≠ 0 := rho_positive.ne'
  have hd : 1+1/rho ≠ 0 := by have := one_div_pos.mpr rho_positive; linarith
  have hr1 : rho+1 ≠ 0 := by linarith [rho_positive]
  field_simp [hr,hr1]
  unfold rho
  linear_combination 3*nu*hs

end
end StrongSilver.Scalar.Silver
