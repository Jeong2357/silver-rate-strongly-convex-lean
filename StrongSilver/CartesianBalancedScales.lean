-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianBalanceRatios

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3000000

/-- Uniform balance on all splitting vertices before a fixed depth. -/
def balancedThrough (φ : ℝ → ℝ) (ε : ℝ) : ℕ → ScheduleTree → Prop
  | 0,_ => True
  | _+1,.leaf _ => False
  | d+1,t@(.split l _ r) => SilverBalanced φ ε t ∧ balancedThrough φ ε d l ∧ balancedThrough φ ε d r

namespace FourGapGroup

theorem balanced_split_scale {φ : ℝ → ℝ} {ε : ℝ} {l r : ScheduleTree} {b : ℝ}
    (hε : ε ≤ 1/100) (h : SilverBalanced φ ε (.split l b r)) :
    (prefixMass φ (.split l b r))/4 ≤ l.prefixMass φ ∧
    (prefixMass φ (.split l b r))/4 ≤ r.prefixMass φ ∧
    l.prefixMass φ ≤ prefixMass φ (.split l b r) ∧
    r.prefixMass φ ≤ prefixMass φ (.split l b r) := by
  have hε1 : ε < 1 := hε.trans_lt (by norm_num)
  have hK := positive_excess_of_balance h hε1
  have hm := (positive_excess_mass_identity φ l r b hK).1
  have hl := abs_le.mp h.2.1
  have hr := abs_le.mp h.2.2.1
  have hk := abs_le.mp h.2.2.2
  have hden := mul_pos rho_positive h.1
  have hl0 := (le_div_iff₀ hden).mp (show 1-ε ≤ l.prefixMass φ/(rho*φ b) by linarith only [hl.1])
  have hl1 := (div_le_iff₀ hden).mp (show l.prefixMass φ/(rho*φ b) ≤ 1+ε by linarith only [hl.2])
  have hr0 := (le_div_iff₀ hden).mp (show 1-ε ≤ r.prefixMass φ/(rho*φ b) by linarith only [hr.1])
  have hr1 := (div_le_iff₀ hden).mp (show r.prefixMass φ/(rho*φ b) ≤ 1+ε by linarith only [hr.2])
  have hk1 := (div_le_iff₀ h.1).mp (show adjustedExcess φ l b/φ b ≤ 1+ε by linarith only [hk.2])
  have hsmall := mul_le_mul_of_nonneg_right hε hden.le
  have hsmall' := mul_le_mul_of_nonneg_right hε h.1.le
  have hρa := mul_le_mul_of_nonneg_right rho_bounds.1.le h.1.le
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [hm,hl0,hr1,hk1,hsmall,hsmall',hρa,h.1]
  · nlinarith only [hm,hr0,hl1,hk1,hsmall,hsmall',hρa,h.1]
  · linarith only [hm,hK,prefixMass_positive φ r]
  · linarith only [hm,hK,prefixMass_positive φ l]

end FourGapGroup

theorem balancedThrough_complete {φ : ℝ → ℝ} {ε : ℝ} {d : ℕ} {t : ScheduleTree}
    (h : balancedThrough φ ε d t) : completeThrough d t := by
  induction d generalizing t with
  | zero => trivial
  | succ d ih =>
    cases t with
    | leaf hword => exact False.elim h
    | split l b r => exact ⟨ih h.2.1,ih h.2.2⟩

theorem balancedThrough_positive {φ : ℝ → ℝ} {ε : ℝ} {d : ℕ} {t : ScheduleTree}
    (hε : ε < 1) (h : balancedThrough φ ε d t) : positiveExcessThrough φ d t := by
  induction d generalizing t with
  | zero => trivial
  | succ d ih =>
    cases t with
    | leaf hword => exact False.elim h
    | split l b r => exact ⟨FourGapGroup.positive_excess_of_balance h.1 hε,ih h.2.1,ih h.2.2⟩

/-- Every depth group retains a polynomially small fraction of its root
mass: the denominator is 4^d. This yields the polylogarithmic scale bound
when d is the logarithmic depth chosen in Lemma 4.2. -/
theorem balanced_frontier_mass_bounds {φ : ℝ → ℝ} {ε : ℝ} (hε : ε ≤ 1/100)
    {d : ℕ} {t : ScheduleTree} (h : balancedThrough φ ε d t)
    {s : ScheduleTree} (hs : s ∈ depthFrontier d t) :
    (1/4:ℝ)^d*t.prefixMass φ ≤ s.prefixMass φ ∧ s.prefixMass φ ≤ t.prefixMass φ := by
  induction d generalizing t with
  | zero =>
    simp only [depthFrontier,List.mem_singleton] at hs
    subst s
    simp only [pow_zero,one_mul,le_refl,and_self]
  | succ d ih =>
    cases t with
    | leaf hword => exact False.elim h
    | split l b r =>
      have hb := FourGapGroup.balanced_split_scale hε h.1
      simp only [depthFrontier,List.mem_append] at hs
      rcases hs with hs | hs
      · obtain ⟨hlo,hhi⟩ := ih h.2.1 hs
        have hp := mul_le_mul_of_nonneg_left hb.1 (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) d)
        refine ⟨?_,hhi.trans hb.2.2.1⟩
        rw [pow_succ]
        nlinarith only [hp,hlo]
      · obtain ⟨hlo,hhi⟩ := ih h.2.2 hs
        have hp := mul_le_mul_of_nonneg_left hb.2.1 (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) d)
        refine ⟨?_,hhi.trans hb.2.2.2⟩
        rw [pow_succ]
        nlinarith only [hp,hlo]

theorem balanced_frontier_inherits {φ : ℝ → ℝ} {ε : ℝ} {d k : ℕ} {t : ScheduleTree}
    (h : balancedThrough φ ε (d+k) t) {s : ScheduleTree} (hs : s ∈ depthFrontier d t) :
    balancedThrough φ ε k s := by
  induction d generalizing t with
  | zero =>
    simp only [depthFrontier,List.mem_singleton] at hs
    subst s
    simpa only [Nat.zero_add] using h
  | succ d ih =>
    rw [Nat.succ_add] at h
    cases t with
    | leaf hword => exact False.elim h
    | split l b r =>
      have hc : balancedThrough φ ε (d+k) l ∧ balancedThrough φ ε (d+k) r := by
        simpa only [Nat.succ_add,balancedThrough] using h.2
      simp only [depthFrontier,List.mem_append] at hs
      exact hs.elim (fun hs => ih hc.1 hs) (fun hs => ih hc.2 hs)

end
end StrongSilver.ScheduleTree
