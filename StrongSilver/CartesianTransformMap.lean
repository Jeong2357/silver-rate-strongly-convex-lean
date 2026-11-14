-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianScheduleTree
import StrongSilver.CappedTransform

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2400000

theorem logarithmicStep_strictMonoOn {μ : ℝ} (hμ : 0 < μ) :
    StrictMonoOn (logarithmicStep μ) {b : ℝ | μ*b < 1} := by
  intro a ha b hb hab
  change μ*a < 1 at ha
  change μ*b < 1 at hb
  have hlog := Real.log_lt_log (by linarith only [hb] : 0 < 1-μ*b)
    (by nlinarith only [hμ,hab] : 1-μ*b < 1-μ*a)
  apply (div_lt_div_iff_of_pos_right hμ).mpr
  linarith only [hlog]

theorem cappedStep_strictMono {μ B : ℝ} (hμ : 0 < μ) (hB : μ*B < 1) : StrictMono (cappedStep μ B) := by
  intro a b hab
  by_cases ha : a ≤ B <;> by_cases hb : b ≤ B
  · simp only [cappedStep,if_pos ha,if_pos hb]
    exact logarithmicStep_strictMonoOn hμ
      ((mul_le_mul_of_nonneg_left ha hμ.le).trans_lt hB)
      ((mul_le_mul_of_nonneg_left hb hμ.le).trans_lt hB) hab
  · simp only [cappedStep,if_pos ha,if_neg hb]
    have hl := logarithmicStep_monotone hμ ha hB
    linarith only [hl,lt_of_not_ge hb]
  · exact False.elim (ha (hab.le.trans hb))
  · simp only [cappedStep,if_neg ha,if_neg hb]
    linarith only [hab]

namespace ScheduleTree

def mapSteps (φ : ℝ → ℝ) : ScheduleTree → ScheduleTree
  | .leaf h => .leaf (h.map φ)
  | .split l b r => .split (l.mapSteps φ) (φ b) (r.mapSteps φ)

@[simp] theorem mapSteps_word (φ : ℝ → ℝ) (t : ScheduleTree) : (t.mapSteps φ).word = t.word.map φ := by
  induction t <;> simp_all [mapSteps,word]

theorem mapSteps_cartesian {φ : ℝ → ℝ} (hφ : StrictMono φ) (hzero : φ 0 = 0)
    {t : ScheduleTree} (hc : t.Cartesian) : (t.mapSteps φ).Cartesian := by
  induction t with
  | leaf hw =>
    intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    have hh := hφ.monotone (hc a ha)
    rwa [hzero] at hh
  | split l b r il ir =>
    refine ⟨il hc.1,ir hc.2.1,?_,?_,?_⟩
    · simpa only [hzero] using hφ hc.2.2.1
    · intro x hx
      rw [mapSteps_word] at hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      exact hφ (hc.2.2.2.1 a ha)
    · intro x hx
      rw [mapSteps_word] at hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      exact hφ.monotone (hc.2.2.2.2 a ha)

theorem capped_map_cartesian {μ B : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B) (hcap : μ*B < 1)
    {t : ScheduleTree} (hc : t.Cartesian) : (t.mapSteps (cappedStep μ B)).Cartesian :=
  mapSteps_cartesian (cappedStep_strictMono hμ hcap)
    (by simp only [cappedStep,if_pos hB,logarithmicStep_zero]) hc

end ScheduleTree
end
end StrongSilver
