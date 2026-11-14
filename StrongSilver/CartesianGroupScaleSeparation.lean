-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianDepthFourGroups

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3000000

private theorem rho_rational_bounds : (12/5:ℝ) < rho ∧ rho < 97/40 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2:ℝ)
  unfold rho
  constructor <;> nlinarith only [hs,hp]

namespace FourGapGroup

theorem reference_total_lower {x : FourPhase.Shape}
    (h : ∀ i, |x i-FourPhase.reference i| ≤ 1/100) : (11/2:ℝ) ≤ FourPhase.totalMass x := by
  have h0 := (abs_le.mp (h 0)).1
  have h1 := (abs_le.mp (h 1)).1
  have h2 := (abs_le.mp (h 2)).1
  have h3 := (abs_le.mp (h 3)).1
  have h4 := (abs_le.mp (h 4)).1
  have h5 := (abs_le.mp (h 5)).1
  have h6 := (abs_le.mp (h 6)).1
  simp only [FourPhase.reference_m0,FourPhase.reference_m1,FourPhase.reference_m2,FourPhase.reference_m3,
    FourPhase.reference_k0,FourPhase.reference_k1,FourPhase.reference_k2,FourPhase.rho_inv_identity] at h0 h1 h2 h3 h4 h5 h6
  unfold FourPhase.totalMass FourPhase.leftMass FourPhase.rightMass
  linarith only [h0,h1,h2,h3,h4,h5,h6,rho_rational_bounds.1]

theorem balanced_right_mass_upper {φ : ℝ → ℝ} {ε : ℝ} {l r : ScheduleTree} {b : ℝ}
    (hε : ε ≤ 1/100) (h : SilverBalanced φ ε (.split l b r)) :
    r.prefixMass φ ≤ (49/20:ℝ)*φ b := by
  have hh := (abs_le.mp h.2.2.1).2
  have hden := mul_pos rho_positive h.1
  have hratio : r.prefixMass φ/(rho*φ b) ≤ 101/100 := by linarith only [hh,hε]
  have hmass := (div_le_iff₀ hden).mp hratio
  have hr := mul_le_mul_of_nonneg_right rho_rational_bounds.2.le h.1.le
  nlinarith only [hmass,hr,h.1]

theorem group_scale_upper {G : FourGapGroup} {φ : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hKL : 0 < adjustedExcess φ G.first G.leftPivot)
    (hKR : 0 < adjustedExcess φ G.third G.rightPivot)
    (hKM : 0 < adjustedExcess φ G.left G.middlePivot)
    (hnear : ∀ i, |G.massShape φ T i-FourPhase.reference i| ≤ 1/100) :
    T ≤ (2/11:ℝ)*G.tree.prefixMass φ := by
  have hh := reference_total_lower hnear
  rw [G.totalMass_massShape φ T hT.ne' hKL hKR hKM] at hh
  have hp := (le_div_iff₀ hT).mp hh
  linarith only [hp]

/-- The sharp scale separation needed at an internal boundary is
strictly below one half; rough factor-two mass bounds would not suffice. -/
theorem internal_retained_scale_upper {φ : ℝ → ℝ} {ε H : ℝ} {l r : ScheduleTree} {b : ℝ}
    (hε : ε ≤ 1/100) (h : SilverBalanced φ ε (.split l b r))
    (hH : H ≤ (2/11:ℝ)*r.prefixMass φ) : H ≤ (9/20:ℝ)*φ b := by
  have hr := balanced_right_mass_upper hε h
  nlinarith only [hr,hH,h.1]

end FourGapGroup

theorem depthFrontier_add (d k : ℕ) (t : ScheduleTree) :
    depthFrontier (d+k) t = (depthFrontier d t).flatMap (depthFrontier k) := by
  induction d generalizing t with
  | zero => simp [depthFrontier]
  | succ d ih =>
    cases t with
    | leaf h => cases k <;> simp [depthFrontier]
    | split l p r => simp [depthFrontier,Nat.succ_add,List.flatMap_append,ih]

namespace FourGapGroup

theorem first_in_second_frontier (G : FourGapGroup) : G.first ∈ depthFrontier 2 G.tree := by
  simp [depthFrontier,tree,left,right]

/-- The actual scale of every chronological group has uniform upper
and lower bounds from the original root mass. -/
theorem depth_groups_scale_bounds {φ : ℝ → ℝ} {ε : ℝ} {d : ℕ} {t : ScheduleTree} {b : ℝ}
    (hε : ε ≤ 1/100) (hbal : balancedThrough φ ε (d+2) t)
    {qs : List Group} (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b)
    {q : Group} (hq : q ∈ qs) :
    (1/4:ℝ)^(d+2)*t.prefixMass φ ≤ q.1.first.prefixMass φ ∧
      q.1.first.prefixMass φ ≤ t.prefixMass φ := by
  have hphase : (q.1.tree,q.2) ∈ depthPhases d t b := hqs ▸ List.mem_map.mpr ⟨q,hq,rfl⟩
  have hfront := depthPhases_mem_frontier hphase
  have hfirst : q.1.first ∈ depthFrontier (d+2) t := by
    rw [depthFrontier_add]
    exact List.mem_flatMap.mpr ⟨q.1.tree,hfront,q.1.first_in_second_frontier⟩
  exact balanced_frontier_mass_bounds hε hbal hfirst

theorem depth_group_balances {φ : ℝ → ℝ} {ε : ℝ} {d : ℕ} {t : ScheduleTree} {b : ℝ}
    (hbal : balancedThrough φ ε (d+2) t)
    {qs : List Group} (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b)
    {q : Group} (hq : q ∈ qs) :
    SilverBalanced φ ε q.1.left ∧ SilverBalanced φ ε q.1.right ∧ SilverBalanced φ ε q.1.tree := by
  have hphase : (q.1.tree,q.2) ∈ depthPhases d t b := hqs ▸ List.mem_map.mpr ⟨q,hq,rfl⟩
  have hh := balanced_frontier_inherits hbal (depthPhases_mem_frontier hphase)
  exact ⟨hh.2.1.1,hh.2.2.1,hh.1⟩

end FourGapGroup
end
end StrongSilver.ScheduleTree
