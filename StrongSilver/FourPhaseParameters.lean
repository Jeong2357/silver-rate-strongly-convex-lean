-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Constants
import Mathlib.Tactic

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2200000

/-- Coordinates 0..3 are the four normalized masses, 4..6 are the three
internal excesses, and coordinate 7 is the joining offset. -/
abbrev Shape := Fin 8 → ℝ

def t0 (x : Shape) : ℝ := x 0+x 4
def t1 (x : Shape) : ℝ := x 1+x 5
def t2 (x : Shape) : ℝ := x 2+x 6
def totalTime (x : Shape) : ℝ := t0 x+t1 x+t2 x
def leftMass (x : Shape) : ℝ := x 0+x 4+x 1
def rightMass (x : Shape) : ℝ := x 2+x 6+x 3
def totalMass (x : Shape) : ℝ := leftMass x+x 5+rightMass x
def q (x : Shape) : ℝ := x 3+x 7
def a (x : Shape) : ℝ := q x/totalTime x
def bodyScale (x : Shape) : ℝ := (1+a x)*q x
def upperTime (x : Shape) : ℝ := x 5+t2 x
def theta (x : Shape) : ℝ := t2 x/x 5
def b1sq (x : Shape) : ℝ := bodyScale x*(1/upperTime x-1/totalTime x)
def b2sq (x : Shape) : ℝ := bodyScale x*(1/x 6-1/upperTime x)
def r2 (x : Shape) : ℝ := (x 1*theta x-totalTime x*b1sq x/b2sq x)/t0 x
def v3sq (x : Shape) : ℝ := (1+x 1/x 4)*theta x*(r2 x+theta x)*b2sq x-(r2 x+theta x)^2*b2sq x

def gain (x : Shape) : ℝ := Real.log (x 5*totalMass x/(leftMass x*rightMass x))
def gainLeft (x : Shape) : ℝ := Real.log (x 4*leftMass x/(x 0*x 1))
def gainRight (x : Shape) : ℝ := Real.log (x 6*rightMass x/(x 2*x 3))
def gainCoefficient (x : Shape) : ℝ := leftMass x*t2 x/(x 5*totalTime x)

def reference : Shape := ![1,1,1,1,rho⁻¹,1,rho⁻¹,0]

theorem totalTime_sub_upperTime (x : Shape) : totalTime x-upperTime x = leftMass x := by
  unfold totalTime upperTime leftMass t0 t1 t2
  ring

theorem totalMass_eq (x : Shape) : totalMass x = totalTime x+x 3 := by
  unfold totalMass totalTime leftMass rightMass t0 t1 t2
  ring

theorem a_mul_totalTime (x : Shape) (hT : totalTime x ≠ 0) : a x*totalTime x = q x := by
  exact div_mul_cancel₀ _ hT

theorem bodyScale_eq (x : Shape) (hT : totalTime x ≠ 0) :
    bodyScale x = q x*(totalMass x+x 7)/totalTime x := by
  rw [totalMass_eq]
  unfold bodyScale a q
  field_simp
  <;> ring

theorem b1sq_identity (x : Shape) (hT : totalTime x ≠ 0) (hU : upperTime x ≠ 0) :
    totalTime x*b1sq x = leftMass x*bodyScale x/upperTime x := by
  have hm := totalTime_sub_upperTime x
  unfold b1sq
  field_simp
  linear_combination bodyScale x*hm

theorem b2sq_identity (x : Shape) (hk : x 6 ≠ 0) (hU : upperTime x ≠ 0) :
    x 6*upperTime x*b2sq x = bodyScale x*(x 5+x 2) := by
  unfold b2sq
  field_simp [hk,hU]
  unfold upperTime t2
  ring

theorem r2_identity (x : Shape) (ht : t0 x ≠ 0) (hb : b2sq x ≠ 0) :
    t0 x*r2 x*b2sq x = x 1*theta x*b2sq x-totalTime x*b1sq x := by
  unfold r2
  field_simp

theorem v3sq_factor (x : Shape) :
    v3sq x = (r2 x+theta x)*((x 1/x 4)*theta x-r2 x)*b2sq x := by
  unfold v3sq
  ring

end
end StrongSilver.FourPhase
