-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseQueryFamily
import StrongSilver.FourPhaseQuerySource
import StrongSilver.FourPhaseSuffixBounds

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 3000000

variable {x : Shape} (R : Regular x)
variable {ι : Type*} (hz : 0 ≤ x 7) (ha : a x ≤ 1/2)
    (hm : ∀ i : Fin 3, (1/2:ℝ) ≤ x (i.castLE (by decide : 3 ≤ 8)))
    (hzsmall : x 7 ≤ 1/16) {T : ℝ} (hT : 0 < T)
    (phase : ι → Fin 4) (c s : ι → ℝ) (hc : ∀ j, 1/2 ≤ c j) (hs : ∀ j, 0 ≤ s j)
include R

/-- The four-plane family renews all the source inequalities in (4.18)
with zero offset. No compatibility condition with an old family is
assumed or asserted by this local renewal lemma. -/
theorem queryFamily_renewal (hTq : totalTime x+q x ≤ 6)
    (ht0 : 1 ≤ t0 x) (ht1 : 1 ≤ t1 x) :
    FourPhaseSuffixBounds (queryFamily R hz ha hm hzsmall hT phase c s hc hs) (source x) T 0 := by
  refine ⟨source_nonzero R,hT,le_refl _,?_,?_,?_,?_⟩
  · intro j
    exact source_queries_nonnegative R (phase j) (hs j) (by linarith only [hc j])
  · intro j
    change 0 ≤ inner ℝ (source x) ((1/T) • slope x (phase j))
    rw [real_inner_smul_right]
    exact mul_nonneg (one_div_pos.mpr hT).le (source_slopes_nonnegative R (phase j))
  · intro j
    change inner ℝ (source x) ((1/T) • slope x (phase j)) ≤ (11/(10*T))*‖source x‖^2
    rw [real_inner_smul_right]
    have hcap := source_slopes_upper R ht0 ht1 (phase j)
    have hh := mul_le_mul_of_nonneg_left hcap (one_div_pos.mpr hT).le
    have hp := mul_nonneg (one_div_pos.mpr hT).le (sq_nonneg ‖source x‖)
    have he : (11/(10*T))*‖source x‖^2 = (11/10:ℝ)*((1/T)*‖source x‖^2) := by
      field_simp <;> ring
    rw [he]
    nlinarith only [hh,hp]
  · intro j
    change max (inner ℝ (source x) (c j • (foot x (phase j)+s j • slope x (phase j)))-0*‖source x‖^2) 0/(8*T) ≤
      planeValue x (phase j) (c j • (foot x (phase j)+s j • slope x (phase j)))/T
    have hp := source_queries_nonnegative R (phase j) (hs j) (show 0 ≤ c j by linarith only [hc j])
    rw [zero_mul,sub_zero,max_eq_left hp]
    have hh := query_height_renewal R hz ha hTq hm hzsmall (phase j) (hc j) (hs j)
    have he : inner ℝ (source x) (c j • (foot x (phase j)+s j • slope x (phase j)))/(8*T) =
        (inner ℝ (source x) (c j • (foot x (phase j)+s j • slope x (phase j)))/8)/T := by
      field_simp <;> ring
    rw [he]
    apply div_le_div_of_nonneg_right _ hT.le
    linarith only [hh]

theorem queryFamily_gate (ht0 : 1 ≤ t0 x) (ht1 : 1 ≤ t1 x) {η : ℝ}
    (hη : 0 ≤ η) (hintercept : η*‖source x‖^2 ≤ a x*x 7) :
    (queryFamily R hz ha hm hzsmall hT phase c s hc hs).Gate (source x) η := by
  intro j
  change planeValue x (phase j) (c j • (foot x (phase j)+s j • slope x (phase j)))/T+
    inner ℝ ((1/T) • slope x (phase j))
      (η • source x-c j • (foot x (phase j)+s j • slope x (phase j))) ≤ 0
  rw [real_inner_smul_left,inner_sub_right,real_inner_smul_right]
  rw [real_inner_comm (source x) (slope x (phase j))]
  have hcap := source_slopes_upper R ht0 ht1 (phase j)
  have hh := (mul_le_mul_of_nonneg_left hcap hη).trans hintercept
  have hp := mul_le_mul_of_nonneg_left hh (one_div_pos.mpr hT).le
  unfold planeValue
  simp only [div_eq_mul_inv,one_div] at hp ⊢
  nlinarith only [hp]

end
end StrongSilver.FourPhase
