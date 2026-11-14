-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 1400000

abbrev Coordinates := WithLp 2 (WithLp 2 (ℝ × ℝ) × WithLp 2 (ℝ × ℝ))

def point (a b c d : ℝ) : Coordinates :=
  WithLp.toLp 2 (WithLp.toLp 2 (a,b),WithLp.toLp 2 (c,d))

theorem point_inner (a b c d e f g h : ℝ) :
    inner ℝ (point a b c d) (point e f g h) = a*e+b*f+c*g+d*h := by
  change (inner ℝ a e+inner ℝ b f)+(inner ℝ c g+inner ℝ d h) = _
  simp only [Real.inner_apply]
  ring

theorem point_norm_sq (a b c d : ℝ) : ‖point a b c d‖^2 = a^2+b^2+c^2+d^2 := by
  rw [← real_inner_self_eq_norm_sq,point_inner]
  ring

theorem point_add (a b c d e f g h : ℝ) :
    point a b c d+point e f g h = point (a+e) (b+f) (c+g) (d+h) := rfl

theorem point_sub (a b c d e f g h : ℝ) :
    point a b c d-point e f g h = point (a-e) (b-f) (c-g) (d-h) := rfl

theorem point_smul (s a b c d : ℝ) : s • point a b c d = point (s*a) (s*b) (s*c) (s*d) := rfl

@[simp] theorem point_zero : point 0 0 0 0 = 0 := rfl

def axis : Coordinates := point 1 0 0 0

theorem axis_inner_point (a b c d : ℝ) : inner ℝ axis (point a b c d) = a := by
  simp only [axis,point_inner,one_mul,zero_mul,add_zero]

theorem point_inner_axis (a b c d : ℝ) : inner ℝ (point a b c d) axis = a := by
  simp only [axis,point_inner,mul_one,mul_zero,add_zero]

theorem axis_unit : inner ℝ axis axis = 1 := by
  rw [axis,point_inner]
  norm_num

theorem point_ne_zero_of_second_ne {a b c d : ℝ} (hb : b ≠ 0) : point a b c d ≠ 0 := by
  intro he
  have hh := point_inner 0 1 0 0 a b c d
  rw [he,inner_zero_right] at hh
  norm_num at hh
  exact hb hh.symm

end
end StrongSilver.FourPhase
