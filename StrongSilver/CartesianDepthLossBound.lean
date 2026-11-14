-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianSequenceLossBound
import StrongSilver.CartesianDepthFourGroups

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3600000

theorem levelSum_parent_children (f : ScheduleTree → ℝ) (hf : ∀ h, f (.leaf h) = 0)
    (d : ℕ) (t : ScheduleTree) :
    levelSum (fun s => f s+levelSum f 1 s) d t = levelSum f d t+levelSum f (d+1) t := by
  induction d generalizing t with
  | zero => cases t <;> simp [levelSum,hf]
  | succ d ih => cases t <;> simp only [levelSum,ih] <;> ring

namespace FourGapGroup

theorem depth_groups_three_sum (f : ScheduleTree → ℝ) (hf : ∀ h, f (.leaf h) = 0)
    {d : ℕ} {t : ScheduleTree} {b : ℝ} {qs : List Group}
    (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b) :
    (qs.map fun q => f q.1.tree+f q.1.left+f q.1.right).sum = levelSum f d t+levelSum f (d+1) t := by
  have hm := congrArg (List.map Prod.fst) hqs
  simp only [List.map_map,depthPhases_map_fst,Function.comp_def] at hm
  have hh := congrArg (fun ts : List ScheduleTree => (ts.map fun s => f s+levelSum f 1 s).sum) hm
  rw [frontier_sum_eq_levelSum _ (fun h => by simp [hf,levelSum]),levelSum_parent_children f hf] at hh
  simpa only [List.map_map,Function.comp_def,levelSum,tree,left,right,add_assoc] using hh

theorem depth_absolute_gain_sum {μ : ℝ} {d : ℕ} {t : ScheduleTree} {b : ℝ} {qs : List Group}
    (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b) :
    (qs.map fun q => absoluteThreeGain μ q.1).sum =
      levelSum (fun s => |rootGain (logarithmicStep μ) s|) d t+
      levelSum (fun s => |rootGain (logarithmicStep μ) s|) (d+1) t :=
  depth_groups_three_sum (fun s => |rootGain (logarithmicStep μ) s|) (fun h => by simp [rootGain]) hqs

/-- Explicit finite form of all depth-construction error terms. The
factor 2^d only multiplies curvature, gate and input-offset errors. -/
theorem depth_sequence_loss_bound {δ c μ B ε L U Zmax η Z : ℝ} {d : ℕ} {t : ScheduleTree} {b : ℝ} {qs : List Group}
    (W : UniformGroups δ c μ B ε L U qs) (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b)
    (hbal : balancedThrough (logarithmicStep μ) ε (d+2) t) (hε : ε ≤ 1/100)
    (hL : 0 < L) (hμ : 0 ≤ μ) (hμB : μ*B ≤ 1/2) (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hZ : 0 ≤ Z) (hZmax : Z ≤ Zmax) :
    sequenceLoss μ ε η qs Z ≤
      (ε+μ*t.prefixMass (logarithmicStep μ))*(levelSum (fun s => |rootGain (logarithmicStep μ) s|) d t+
        levelSum (fun s => |rootGain (logarithmicStep μ) s|) (d+1) t)+
      (2:ℝ)^d*(μ*t.prefixMass (logarithmicStep μ)+μ*U+η+2*U*Zmax/L) := by
  have hscales : ∀ q ∈ qs, groupScale μ q ≤ t.prefixMass (logarithmicStep μ) :=
    fun q hq => (depth_groups_scale_bounds hε hbal hqs hq).2
  have hh := sequenceLoss_uniform_bound (η := η) W hL hμ hμB hscales hZ hZmax
  rw [depth_absolute_gain_sum hqs] at hh
  have hcount : (qs.length:ℝ) ≤ (2:ℝ)^d := by exact_mod_cast depth_groups_count hqs
  have herror : 0 ≤ μ*t.prefixMass (logarithmicStep μ)+μ*U+η+2*U*Zmax/L := by
    have hZmax0 := hZ.trans hZmax
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg hμ (prefixMass_positive _ _).le) (mul_nonneg hμ hU)) hη)
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hU) hZmax0) hL.le)
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcount herror))

end FourGapGroup
end
end StrongSilver.ScheduleTree
