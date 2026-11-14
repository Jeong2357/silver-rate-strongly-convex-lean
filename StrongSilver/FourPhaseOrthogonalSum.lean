-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseSuffixBounds

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι κ : Type*}
set_option maxHeartbeats 1800000

/-- Adding retained planes orthogonal to the new source preserves all
zero-offset source bounds. The cross inequalities are the two verified
finite interpolation comparisons. -/
theorem FourPhaseSuffixBounds.sum_orthogonal {F : SupportFamily ι V} {G : SupportFamily κ V}
    {Y : V} {T : ℝ}
    (B : FourPhaseSuffixBounds F Y T 0)
    (hFG : ∀ i j, F.d i+inner ℝ (F.g i) (G.z j-F.z i) ≤ G.d j)
    (hGF : ∀ j i, G.d j+inner ℝ (G.g j) (F.z i-G.z j) ≤ F.d i)
    (hz : ∀ j, inner ℝ Y (G.z j) = 0) (hg : ∀ j, inner ℝ Y (G.g j) = 0) :
    FourPhaseSuffixBounds (F.sum G hFG hGF) Y T 0 := by
  refine ⟨B.source_nonzero,B.scale_positive,B.offset_nonnegative,?_,?_,?_,?_⟩
  · intro i; cases i with
    | inl i => exact B.point_positive i
    | inr j => exact (hz j).ge
  · intro i; cases i with
    | inl i => exact B.slope_positive i
    | inr j => exact (hg j).ge
  · intro i; cases i with
    | inl i => exact B.slope_upper i
    | inr j =>
      change inner ℝ Y (G.g j) ≤ (11/(10*T))*‖Y‖^2
      rw [hg]
      exact mul_nonneg (div_nonneg (by norm_num) (mul_pos (by norm_num) B.scale_positive).le) (sq_nonneg _)
  · intro i; cases i with
    | inl i => exact B.height_lower i
    | inr j =>
      change max (inner ℝ Y (G.z j)-0*‖Y‖^2) 0/(8*T) ≤ G.d j
      rw [hz,zero_mul,sub_zero,max_self,zero_div]
      exact G.nonnegative j

theorem SupportFamily.sum_gate_orthogonal (F : SupportFamily ι V) (G : SupportFamily κ V)
    {Y : V} {η : ℝ}
    (hFG : ∀ i j, F.d i+inner ℝ (F.g i) (G.z j-F.z i) ≤ G.d j)
    (hGF : ∀ j i, G.d j+inner ℝ (G.g j) (F.z i-G.z j) ≤ F.d i)
    (hgate : F.Gate Y η) (hg : ∀ j, inner ℝ Y (G.g j) = 0) :
    (F.sum G hFG hGF).Gate Y η := by
  intro i
  cases i with
  | inl i => exact hgate i
  | inr j =>
    change G.d j+inner ℝ (G.g j) (η • Y-G.z j) ≤ 0
    rw [inner_sub_right,real_inner_smul_right,real_inner_comm Y (G.g j),hg,mul_zero,zero_sub]
    have hh := G.origin j
    linarith only [hh]

end
end StrongSilver
