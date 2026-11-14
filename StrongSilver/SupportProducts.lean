-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportFamilies
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace StrongSilver.SupportFamily
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {ι : Type*}

def prod (F : SupportFamily ι V) (G : SupportFamily ι W) : SupportFamily ι (WithLp 2 (V × W)) where
  z := fun i => WithLp.toLp 2 (F.z i,G.z i)
  g := fun i => WithLp.toLp 2 (F.g i,G.g i)
  d := fun i => F.d i+G.d i
  nonnegative := fun i => add_nonneg (F.nonnegative i) (G.nonnegative i)
  origin := by
    intro i
    change F.d i+G.d i ≤ inner ℝ (F.g i) (F.z i)+inner ℝ (G.g i) (G.z i)
    exact add_le_add (F.origin i) (G.origin i)
  supports := by
    intro i j
    change F.d i+G.d i+(inner ℝ (F.g i) (F.z j-F.z i)+inner ℝ (G.g i) (G.z j-G.z i)) ≤ F.d j+G.d j
    linarith only [F.supports i j,G.supports i j]

def zeroSlopes (x : ι → V) : SupportFamily ι V where
  z := x
  g := fun _ => 0
  d := fun _ => 0
  nonnegative := fun _ => le_refl _
  origin := by intro i; rw [inner_zero_left]
  supports := by intro i j; rw [inner_zero_left,add_zero]

end
end StrongSilver.SupportFamily
