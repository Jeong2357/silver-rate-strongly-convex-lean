-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseUniformBox

namespace StrongSilver.FourPhase
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2400000

structure JoiningGeometry (x : Shape) : Prop where
  regular : Regular x
  time0_lower : 1 ≤ t0 x
  time1_lower : 1 ≤ t1 x
  a_lower : 1/8 ≤ a x
  a_upper : a x ≤ 9/40
  total_upper : totalTime x+q x ≤ 6
  source_norm_upper : ‖source x‖^2 ≤ 64
  masses_lower : ∀ i : Fin 3, (1/2:ℝ) ≤ x (i.castLE (by decide : 3 ≤ 8))

theorem exists_joining_box : ∃ δ > 0, δ ≤ 1/16 ∧ ∀ x : Shape,
    (∀ i, |x i-reference i| ≤ δ) → JoiningGeometry x := by
  have hρ : (20/9:ℝ) < rho := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg (2:ℝ)
    unfold rho
    nlinarith only [hh,hp]
  have ha : a reference < 9/40 := by
    rw [a_reference]
    exact (div_lt_iff₀ (mul_pos (by norm_num) rho_positive)).mpr (by linarith only [hρ])
  have he := (tendsto_order.1 continuousAt_a_reference).2 (9/40) ha
  obtain ⟨d,hd,hball⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨b,hb,huniform⟩ := exists_uniform_box
  let δ := min b (min (d/2) (1/16))
  have hδ : 0 < δ := lt_min hb (lt_min (half_pos hd) (by norm_num))
  have hδb : δ ≤ b := min_le_left _ _
  have hδd : δ ≤ d/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ16 : δ ≤ 1/16 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,hδ16,fun x hx => ?_⟩
  obtain ⟨R,ht0,ht1,ha0,ha1,hT,hX⟩ := huniform x (fun i => (hx i).trans hδb)
  have hxd : dist x reference < d := by
    have hh : dist x reference ≤ δ := (dist_pi_le_iff hδ.le).mpr
      (fun i => by simpa only [Real.dist_eq] using hx i)
    exact hh.trans_lt (hδd.trans_lt (by linarith only [hd]))
  refine ⟨R,ht0,ht1,ha0,(hball hxd).le,hT,hX,?_⟩
  intro i
  fin_cases i
  all_goals first
    | (have hh : |x 0-1| ≤ δ := by simpa only [reference_m0] using hx 0
       have hl := (abs_le.mp hh).1
       change (1/2:ℝ) ≤ x 0
       linarith only [hl,hδ16])
    | (have hh : |x 1-1| ≤ δ := by simpa only [reference_m1] using hx 1
       have hl := (abs_le.mp hh).1
       change (1/2:ℝ) ≤ x 1
       linarith only [hl,hδ16])
    | (have hh : |x 2-1| ≤ δ := by simpa only [reference_m2] using hx 2
       have hl := (abs_le.mp hh).1
       change (1/2:ℝ) ≤ x 2
       linarith only [hl,hδ16])

end
end StrongSilver.FourPhase
