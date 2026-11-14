-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianFourGapGroups
import StrongSilver.FourPhaseParameters

namespace StrongSilver.ScheduleTree.FourGapGroup
noncomputable section
set_option maxHeartbeats 2400000

def massShape (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) : FourPhase.Shape :=
  ![G.first.prefixMass φ/T,G.second.prefixMass φ/T,G.third.prefixMass φ/T,G.fourth.prefixMass φ/T,
    adjustedExcess φ G.first G.leftPivot/T,adjustedExcess φ G.left G.middlePivot/T,
    adjustedExcess φ G.third G.rightPivot/T,0]

@[simp] theorem shape_m0 (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) : massShape G φ T 0 = G.first.prefixMass φ/T := rfl
@[simp] theorem shape_m1 (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) : massShape G φ T 1 = G.second.prefixMass φ/T := rfl
@[simp] theorem shape_m2 (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) : massShape G φ T 2 = G.third.prefixMass φ/T := rfl
@[simp] theorem shape_m3 (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) : massShape G φ T 3 = G.fourth.prefixMass φ/T := rfl
@[simp] theorem shape_k0 (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) : massShape G φ T 4 = adjustedExcess φ G.first G.leftPivot/T := rfl
@[simp] theorem shape_k1 (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) : massShape G φ T 5 = adjustedExcess φ G.left G.middlePivot/T := rfl
@[simp] theorem shape_k2 (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) : massShape G φ T 6 = adjustedExcess φ G.third G.rightPivot/T := rfl
@[simp] theorem shape_offset (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) : massShape G φ T 7 = 0 := rfl

theorem leftMass_massShape (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) (hT : T ≠ 0)
    (hK : 0 < adjustedExcess φ G.first G.leftPivot) :
    FourPhase.leftMass (G.massShape φ T) = G.left.prefixMass φ/T := by
  have hm := (positive_excess_mass_identity φ G.first G.second G.leftPivot hK).1
  change G.left.prefixMass φ = _ at hm
  rw [FourPhase.leftMass,shape_m0,shape_k0,shape_m1]
  field_simp
  linear_combination -hm

theorem rightMass_massShape (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) (hT : T ≠ 0)
    (hK : 0 < adjustedExcess φ G.third G.rightPivot) :
    FourPhase.rightMass (G.massShape φ T) = G.right.prefixMass φ/T := by
  have hm := (positive_excess_mass_identity φ G.third G.fourth G.rightPivot hK).1
  change G.right.prefixMass φ = _ at hm
  rw [FourPhase.rightMass,shape_m2,shape_k2,shape_m3]
  field_simp
  linear_combination -hm

theorem totalMass_massShape (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) (hT : T ≠ 0)
    (hKL : 0 < adjustedExcess φ G.first G.leftPivot)
    (hKR : 0 < adjustedExcess φ G.third G.rightPivot)
    (hK : 0 < adjustedExcess φ G.left G.middlePivot) :
    FourPhase.totalMass (G.massShape φ T) = G.tree.prefixMass φ/T := by
  have hm := (positive_excess_mass_identity φ G.left G.right G.middlePivot hK).1
  change G.tree.prefixMass φ = _ at hm
  rw [FourPhase.totalMass,G.leftMass_massShape φ T hT hKL,G.rightMass_massShape φ T hT hKR,shape_k1]
  field_simp
  linear_combination -hm

/-- The three geometric logarithmic gains on rescaled exact tree masses
are precisely the three gains of the actual root and its two children. -/
theorem gains_massShape (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) (hT : T ≠ 0)
    (hKL : 0 < adjustedExcess φ G.first G.leftPivot)
    (hKR : 0 < adjustedExcess φ G.third G.rightPivot)
    (hK : 0 < adjustedExcess φ G.left G.middlePivot) :
    FourPhase.gain (G.massShape φ T) = rootGain φ G.tree ∧
      FourPhase.gainLeft (G.massShape φ T) = rootGain φ G.left ∧
      FourPhase.gainRight (G.massShape φ T) = rootGain φ G.right := by
  have hL := (prefixMass_positive φ G.left).ne'
  have hR := (prefixMass_positive φ G.right).ne'
  have h0 := (prefixMass_positive φ G.first).ne'
  have h1 := (prefixMass_positive φ G.second).ne'
  have h2 := (prefixMass_positive φ G.third).ne'
  have h3 := (prefixMass_positive φ G.fourth).ne'
  refine ⟨?_,?_,?_⟩
  · rw [FourPhase.gain,G.leftMass_massShape φ T hT hKL,G.rightMass_massShape φ T hT hKR,
      G.totalMass_massShape φ T hT hKL hKR hK,shape_k1]
    change Real.log ((adjustedExcess φ G.left G.middlePivot/T)*(G.tree.prefixMass φ/T)/
      ((G.left.prefixMass φ/T)*(G.right.prefixMass φ/T))) = Real.log _
    congr 1
    field_simp <;> rfl
  · rw [FourPhase.gainLeft,G.leftMass_massShape φ T hT hKL,shape_k0,shape_m0,shape_m1]
    change Real.log ((adjustedExcess φ G.first G.leftPivot/T)*(G.left.prefixMass φ/T)/
      ((G.first.prefixMass φ/T)*(G.second.prefixMass φ/T))) = Real.log _
    congr 1
    field_simp <;> rfl
  · rw [FourPhase.gainRight,G.rightMass_massShape φ T hT hKR,shape_k2,shape_m2,shape_m3]
    change Real.log ((adjustedExcess φ G.third G.rightPivot/T)*(G.right.prefixMass φ/T)/
      ((G.third.prefixMass φ/T)*(G.fourth.prefixMass φ/T))) = Real.log _
    congr 1
    field_simp <;> rfl

end
end StrongSilver.ScheduleTree.FourGapGroup
