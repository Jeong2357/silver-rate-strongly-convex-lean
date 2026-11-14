-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianUniformGroupReady

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3000000

theorem balancedThrough_prefix {φ : ℝ → ℝ} {ε : ℝ} {d k : ℕ} {t : ScheduleTree}
    (h : balancedThrough φ ε (d+k) t) : balancedThrough φ ε d t := by
  induction d generalizing t with
  | zero => trivial
  | succ d ih =>
    rw [Nat.succ_add] at h
    cases t with
    | leaf hword => exact False.elim h
    | split l b r => exact ⟨h.1,ih h.2.1,ih h.2.2⟩

theorem depthPhases_ne_nil (d : ℕ) (t : ScheduleTree) (b : ℝ) : depthPhases d t b ≠ [] := by
  induction d generalizing t b with
  | zero => simp [depthPhases]
  | succ d ih =>
    cases t with
    | leaf h => simp [depthPhases]
    | split l p r =>
      intro h
      have hl := (List.append_eq_nil_iff.mp h).1
      exact ih l p hl

namespace FourGapGroup

/-- Uniform finite bounds on the actual original depth groups. All
fields are numeric; the backward trajectory is constructed afterwards. -/
structure UniformGroups (δ c μ B ε L U : ℝ) (qs : List Group) : Prop where
  data : ∀ q ∈ qs, BalancedGroupData q.1 μ (groupScale μ q) q.2 ε
  near : ∀ q ∈ qs, ε+μ*groupScale μ q ≤ δ
  scale_lower : ∀ q ∈ qs, L ≤ groupScale μ q
  scale_upper : ∀ q ∈ qs, groupScale μ q ≤ (2/11:ℝ)*q.1.tree.prefixMass (logarithmicStep μ)
  boundary_upper : ∀ q ∈ qs, q.2 ≤ U
  time_lower : ∀ q ∈ qs, (19/20:ℝ)*cappedStep μ B q.2 ≤
    groupScale μ q*FourPhase.lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2)
  time_upper : ∀ q ∈ qs, groupScale μ q*FourPhase.lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2) ≤ 2*q.2
  negative_budget : ∀ q ∈ qs, ∀ i : Fin 3, 2*U*Scalar.SignedIntervals.negativeMass (q.1.gaps i.castSucc) ≤ c*L^2

namespace UniformGroups
variable {δ c μ B ε L U : ℝ} {qs : List Group}

theorem restrict (W : UniformGroups δ c μ B ε L U qs) {ps : List Group} (hps : ps.Sublist qs) :
    UniformGroups δ c μ B ε L U ps := {
  data := fun q hq => W.data q (hps.subset hq)
  near := fun q hq => W.near q (hps.subset hq)
  scale_lower := fun q hq => W.scale_lower q (hps.subset hq)
  scale_upper := fun q hq => W.scale_upper q (hps.subset hq)
  boundary_upper := fun q hq => W.boundary_upper q (hps.subset hq)
  time_lower := fun q hq => W.time_lower q (hps.subset hq)
  time_upper := fun q hq => W.time_upper q (hps.subset hq)
  negative_budget := fun q hq => W.negative_budget q (hps.subset hq)
}

theorem first_scale_lower (W : UniformGroups δ c μ B ε L U qs) (hqs : qs ≠ []) (H : ℝ) :
    L ≤ firstScale μ qs H := by
  cases qs with
  | nil => exact False.elim (hqs rfl)
  | cons q qs => exact W.scale_lower q (by simp)

theorem first_scale_upper (W : UniformGroups δ c μ B ε L U qs) {d : ℕ} {t : ScheduleTree} {b : ℝ}
    (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b)
    (hε : ε ≤ 1/100) (hbal : balancedThrough (logarithmicStep μ) ε d t) (H : ℝ) :
    firstScale μ qs H ≤ (2/11:ℝ)*t.prefixMass (logarithmicStep μ) := by
  cases qs with
  | nil =>
    have hh : depthPhases d t b = [] := hqs.symm
    exact False.elim (depthPhases_ne_nil d t b hh)
  | cons q qs =>
    have hphase : (q.1.tree,q.2) ∈ depthPhases d t b := hqs ▸ List.mem_map.mpr ⟨q,by simp,rfl⟩
    have hm := (balanced_frontier_mass_bounds hε hbal (depthPhases_mem_frontier hphase)).2
    have hs := W.scale_upper q (by simp)
    exact hs.trans (mul_le_mul_of_nonneg_left hm (by norm_num))

end UniformGroups
end FourGapGroup
end
end StrongSilver.ScheduleTree
