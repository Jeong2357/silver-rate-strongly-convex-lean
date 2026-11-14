-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SilverBalanceParameters
import StrongSilver.CartesianGroupMassShape

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2600000

/-- Balance is expressed by the three dimensionless ratios at a split.
The later height estimates will establish these inequalities for good vertices. -/
def SilverBalanced (φ : ℝ → ℝ) (ε : ℝ) : ScheduleTree → Prop
  | .leaf _ => False
  | .split l b r => 0 < φ b ∧
      |l.prefixMass φ/(rho*φ b)-1| ≤ ε ∧
      |r.prefixMass φ/(rho*φ b)-1| ≤ ε ∧
      |adjustedExcess φ l b/φ b-1| ≤ ε

namespace FourGapGroup

def balanceRatios (G : FourGapGroup) (φ : ℝ → ℝ) : SilverBalance.Parameters :=
  ![G.first.prefixMass φ/(rho*φ G.leftPivot),
    G.second.prefixMass φ/(rho*φ G.leftPivot),
    G.third.prefixMass φ/(rho*φ G.rightPivot),
    G.fourth.prefixMass φ/(rho*φ G.rightPivot),
    adjustedExcess φ G.first G.leftPivot/φ G.leftPivot,
    adjustedExcess φ G.left G.middlePivot/φ G.middlePivot,
    adjustedExcess φ G.third G.rightPivot/φ G.rightPivot,
    G.left.prefixMass φ/(rho*φ G.middlePivot),
    G.right.prefixMass φ/(rho*φ G.middlePivot)]

@[simp] theorem balanceRatios_0 (G : FourGapGroup) (φ : ℝ → ℝ) :
    G.balanceRatios φ 0 = G.first.prefixMass φ/(rho*φ G.leftPivot) := rfl

@[simp] theorem balanceRatios_1 (G : FourGapGroup) (φ : ℝ → ℝ) :
    G.balanceRatios φ 1 = G.second.prefixMass φ/(rho*φ G.leftPivot) := rfl

@[simp] theorem balanceRatios_2 (G : FourGapGroup) (φ : ℝ → ℝ) :
    G.balanceRatios φ 2 = G.third.prefixMass φ/(rho*φ G.rightPivot) := rfl

@[simp] theorem balanceRatios_3 (G : FourGapGroup) (φ : ℝ → ℝ) :
    G.balanceRatios φ 3 = G.fourth.prefixMass φ/(rho*φ G.rightPivot) := rfl

@[simp] theorem balanceRatios_4 (G : FourGapGroup) (φ : ℝ → ℝ) :
    G.balanceRatios φ 4 = adjustedExcess φ G.first G.leftPivot/φ G.leftPivot := rfl

@[simp] theorem balanceRatios_5 (G : FourGapGroup) (φ : ℝ → ℝ) :
    G.balanceRatios φ 5 = adjustedExcess φ G.left G.middlePivot/φ G.middlePivot := rfl

@[simp] theorem balanceRatios_6 (G : FourGapGroup) (φ : ℝ → ℝ) :
    G.balanceRatios φ 6 = adjustedExcess φ G.third G.rightPivot/φ G.rightPivot := rfl

@[simp] theorem balanceRatios_7 (G : FourGapGroup) (φ : ℝ → ℝ) :
    G.balanceRatios φ 7 = G.left.prefixMass φ/(rho*φ G.middlePivot) := rfl

@[simp] theorem balanceRatios_8 (G : FourGapGroup) (φ : ℝ → ℝ) :
    G.balanceRatios φ 8 = G.right.prefixMass φ/(rho*φ G.middlePivot) := rfl

theorem balanceRatios_close {G : FourGapGroup} {φ : ℝ → ℝ} {ε : ℝ}
    (hL : SilverBalanced φ ε G.left) (hR : SilverBalanced φ ε G.right)
    (hM : SilverBalanced φ ε G.tree) : ∀ i, |G.balanceRatios φ i-1| ≤ ε := by
  intro i
  fin_cases i
  all_goals simp only [balanceRatios,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact hL.2.1
  · exact hL.2.2.1
  · exact hR.2.1
  · exact hR.2.2.1
  · exact hL.2.2.2
  · exact hM.2.2.2
  · exact hR.2.2.2
  · exact hM.2.1
  · exact hM.2.2.1

theorem positive_excess_of_balance {φ : ℝ → ℝ} {ε : ℝ} {l r : ScheduleTree} {b : ℝ}
    (h : SilverBalanced φ ε (.split l b r)) (hε : ε < 1) :
    0 < adjustedExcess φ l b := by
  have hratio := (abs_le.mp h.2.2.2).1
  have hpos : 0 < adjustedExcess φ l b/φ b := by linarith only [hratio,hε]
  exact (div_pos_iff.mp hpos).elim (fun hh => hh.1) (fun hh => False.elim ((not_lt_of_ge h.1.le) hh.2))

theorem balanceRatios_shape {G : FourGapGroup} {φ : ℝ → ℝ}
    (hL : 0 < φ G.leftPivot) (hR : 0 < φ G.rightPivot) (hM : 0 < φ G.middlePivot)
    (hKL : 0 < adjustedExcess φ G.first G.leftPivot)
    (hKR : 0 < adjustedExcess φ G.third G.rightPivot) :
    SilverBalance.shape (G.balanceRatios φ) = G.massShape φ (G.first.prefixMass φ) := by
  have hr : rho ≠ 0 := rho_positive.ne'
  have h0 := (prefixMass_positive φ G.first).ne'
  have hleft := (prefixMass_positive φ G.left).ne'
  have hright := (prefixMass_positive φ G.right).ne'
  have hmassL := (positive_excess_mass_identity φ G.first G.second G.leftPivot hKL).1
  have hmassR := (positive_excess_mass_identity φ G.third G.fourth G.rightPivot hKR).1
  change G.left.prefixMass φ = _ at hmassL
  change G.right.prefixMass φ = _ at hmassR
  have hsL : SilverBalance.leftSum (G.balanceRatios φ) = G.left.prefixMass φ/φ G.leftPivot := by
    simp only [SilverBalance.leftSum,balanceRatios_0,balanceRatios_1,balanceRatios_4]
    field_simp [hr,hL.ne']
    linear_combination -hmassL
  have hsR : SilverBalance.rightSum (G.balanceRatios φ) = G.right.prefixMass φ/φ G.rightPivot := by
    simp only [SilverBalance.rightSum,balanceRatios_2,balanceRatios_3,balanceRatios_6]
    field_simp [hr,hR.ne']
    linear_combination -hmassR
  ext i
  fin_cases i
  all_goals simp only [SilverBalance.shape,Matrix.cons_val_zero',Matrix.cons_val_succ',hsL,hsR,
    massShape,balanceRatios_0,balanceRatios_1,balanceRatios_2,balanceRatios_3,balanceRatios_4,balanceRatios_5,balanceRatios_6,balanceRatios_7,balanceRatios_8]
  all_goals try simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals field_simp [hr,h0,hleft,hright,hL.ne',hR.ne',hM.ne'] <;> ring

/-- On an actual Cartesian four-gap group, three balanced vertices give
exactly the near-reference shape needed by the finite four-phase lemma. -/
theorem exists_balanced_shape_constants : ∃ C > 0, ∃ δ > 0, ∀ G : FourGapGroup,
    ∀ (φ : ℝ → ℝ) (ε : ℝ), 0 ≤ ε → ε ≤ δ →
    SilverBalanced φ ε G.left → SilverBalanced φ ε G.right → SilverBalanced φ ε G.tree →
    ∀ i, |G.massShape φ (G.first.prefixMass φ) i-FourPhase.reference i| ≤ C*ε := by
  obtain ⟨C,hC,d,hd,hbox⟩ := SilverBalance.exists_shape_box
  refine ⟨C,hC,min d (1/2),lt_min hd (by norm_num),?_⟩
  intro G φ ε hε hεδ hL hR hM i
  have hε1 : ε < 1 := (hεδ.trans (min_le_right _ _)).trans_lt (by norm_num)
  have hKL := positive_excess_of_balance hL hε1
  have hKR := positive_excess_of_balance hR hε1
  have h := hbox ε hε (hεδ.trans (min_le_left _ _)) (G.balanceRatios φ)
    (balanceRatios_close hL hR hM) i
  rw [balanceRatios_shape hL.1 hR.1 hM.1 hKL hKR] at h
  exact h

end FourGapGroup
end
end StrongSilver.ScheduleTree
