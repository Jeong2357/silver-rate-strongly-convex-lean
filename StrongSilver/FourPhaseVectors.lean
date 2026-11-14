-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseRegular
import StrongSilver.FourPhaseCoordinates

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2400000

def b1 (x : Shape) : ℝ := Real.sqrt (b1sq x)
def b2 (x : Shape) : ℝ := Real.sqrt (b2sq x)
def v3 (x : Shape) : ℝ := Real.sqrt (v3sq x)

def slope0 (x : Shape) : Coordinates := point (a x) (b1 x) (r2 x*b2 x) (v3 x)
def slope1 (x : Shape) : Coordinates := point (a x) (b1 x) (-theta x*b2 x) 0
def slope2 (x : Shape) : Coordinates := point (a x) (b1 x) (b2 x) 0
def slope3 (_x : Shape) : Coordinates := point (-1) 0 0 0

def start3 (x : Shape) : Coordinates := point (-q x) 0 0 0
def start2 (x : Shape) : Coordinates := start3 x+t2 x • slope2 x
def start1 (x : Shape) : Coordinates := start2 x+t1 x • slope1 x
def source (x : Shape) : Coordinates := start1 x+t0 x • slope0 x

def sourceE2 (x : Shape) : ℝ := b2 x*(t0 x*r2 x-t1 x*theta x+t2 x)

theorem b1_sq {x : Shape} (R : Regular x) : b1 x^2 = b1sq x := Real.sq_sqrt R.b1sq_positive.le
theorem b2_sq {x : Shape} (R : Regular x) : b2 x^2 = b2sq x := Real.sq_sqrt R.b2sq_positive.le
theorem v3_sq {x : Shape} (R : Regular x) : v3 x^2 = v3sq x := Real.sq_sqrt R.v3sq_positive.le

theorem theta_mul_k1 {x : Shape} (R : Regular x) : theta x*x 5 = t2 x := div_mul_cancel₀ _ R.k1_positive.ne'

theorem source_formula {x : Shape} (R : Regular x) :
    source x = point 0 (totalTime x*b1 x) (sourceE2 x) (t0 x*v3 x) := by
  have ha := a_mul_totalTime x R.totalTime_positive.ne'
  unfold totalTime at ha
  simp only [source,start1,start2,start3,slope0,slope1,slope2,point_smul,point_add]
  unfold sourceE2 totalTime
  congr 1 <;> (try ring) <;> linear_combination ha

theorem sourceE2_mul_b2 {x : Shape} (R : Regular x) : sourceE2 x*b2 x = -totalTime x*b1sq x := by
  have hr := r2_identity x R.t0_positive.ne' R.b2sq_positive.ne'
  have hb := b2_sq R
  have ht := theta_mul_k1 R
  unfold sourceE2 t1
  linear_combination hr+(t0 x*r2 x-(x 1+x 5)*theta x+t2 x)*hb-b2sq x*ht

theorem source_orthogonal_axis {x : Shape} (R : Regular x) : inner ℝ (source x) axis = 0 := by
  rw [source_formula R,point_inner_axis]

theorem source_nonzero {x : Shape} (R : Regular x) : source x ≠ 0 := by
  rw [source_formula R]
  apply point_ne_zero_of_second_ne
  exact (mul_pos R.totalTime_positive (Real.sqrt_pos.mpr R.b1sq_positive)).ne'

theorem source_slope2_inner {x : Shape} (R : Regular x) : inner ℝ (source x) (slope2 x) = 0 := by
  rw [source_formula R,slope2,point_inner]
  have he := sourceE2_mul_b2 R
  have hb := b1_sq R
  linear_combination he+totalTime x*hb

theorem source_slope3_inner {x : Shape} (R : Regular x) : inner ℝ (source x) (slope3 x) = 0 := by
  rw [source_formula R,slope3,point_inner]
  ring

theorem source_slope1_inner {x : Shape} (R : Regular x) :
    inner ℝ (source x) (slope1 x) = totalTime x*b1sq x*(1+theta x) := by
  rw [source_formula R,slope1,point_inner]
  have he := sourceE2_mul_b2 R
  have hb := b1_sq R
  linear_combination -theta x*he+totalTime x*hb

theorem one_add_theta {x : Shape} (R : Regular x) : 1+theta x = upperTime x/x 5 := by
  unfold theta upperTime
  field_simp [R.k1_positive.ne']
  <;> ring

theorem source_slope1_formula {x : Shape} (R : Regular x) :
    inner ℝ (source x) (slope1 x) = leftMass x*bodyScale x/x 5 := by
  rw [source_slope1_inner R,b1sq_identity x R.totalTime_positive.ne' R.upperTime_positive.ne',one_add_theta R]
  have hU := R.upperTime_positive.ne'
  field_simp

end
end StrongSilver.FourPhase
