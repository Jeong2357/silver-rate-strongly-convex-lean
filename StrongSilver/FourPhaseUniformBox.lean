-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseNormGain
import StrongSilver.FourPhaseNeighborhood

namespace StrongSilver.FourPhase
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 3000000

def normPolynomial (x : Shape) : ℝ := totalTime x^2*b1sq x+
    b2sq x*(t0 x*r2 x-t1 x*theta x+t2 x)^2+t0 x^2*v3sq x

theorem normPolynomial_eq {x : Shape} (R : Regular x) : normPolynomial x = ‖source x‖^2 := by
  rw [source_formula R,point_norm_sq]
  unfold normPolynomial sourceE2
  simp only [mul_pow,b1_sq R,b2_sq R,v3_sq R]
  ring

@[fun_prop] theorem continuousAt_v3sq_reference : ContinuousAt v3sq reference := by
  have hk : reference 4 ≠ 0 := by rw [reference_k0]; exact inv_ne_zero rho_positive.ne'
  unfold v3sq
  fun_prop (disch := assumption)

@[fun_prop] theorem continuousAt_normPolynomial_reference : ContinuousAt normPolynomial reference := by
  unfold normPolynomial
  fun_prop

theorem normPolynomial_reference_lt : normPolynomial reference < 64 := by
  rw [normPolynomial_eq regular_reference]
  have hn := normalizedNorm_gain_identity regular_reference
  have hP : normPrefactor reference = 1 := by simp [normPrefactor]
  simp only [gains_reference.1,gains_reference.2.1,gains_reference.2.2,neg_zero,sub_zero,
    Real.exp_zero,sub_self,mul_zero,add_zero] at hn
  unfold normalizedNorm at hn
  rw [hP,mul_one,totalMass_reference] at hn
  have hρ4 : (rho^2)^2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ rho_positive.ne')
  have hnorm : ‖source reference‖^2 = (rho^2)^2 := (div_eq_one_iff_eq hρ4).mp hn
  rw [hnorm]
  have hρ2 : 0 ≤ rho^2 := sq_nonneg _
  have hlt : rho^2 < 7 := by rw [rho_square]; linarith only [rho_bounds.2]
  have hh := mul_self_lt_mul_self hρ2 hlt
  nlinarith only [hh]

/-- A single closed box supplies the strict margins used when joining
an old trajectory and renewing the source inequalities. -/
theorem exists_uniform_box : ∃ δ > 0, ∀ x : Shape,
    (∀ i, |x i-reference i| ≤ δ) →
    Regular x ∧ 1 ≤ t0 x ∧ 1 ≤ t1 x ∧ 1/8 ≤ a x ∧ a x ≤ 1/2 ∧
      totalTime x+q x ≤ 6 ∧ ‖source x‖^2 ≤ 64 := by
  have ht0 : 1 < t0 reference := by rw [t0_reference]; linarith only [rho_bounds.1]
  have ht1 : 1 < t1 reference := by rw [t1_reference]; norm_num
  have ha0 : 1/8 < a reference := by
    rw [a_reference]
    exact (lt_div_iff₀ (mul_pos (by norm_num) rho_positive)).mpr (by linarith only [rho_bounds.2])
  have ha1 : a reference < 1/2 := by
    rw [a_reference]
    exact (div_lt_iff₀ (mul_pos (by norm_num) rho_positive)).mpr (by linarith only [rho_bounds.1])
  have hTq : totalTime reference+q reference < 6 := by
    rw [totalTime_reference,q_reference]
    have hh := sqrt_two_bounds.2
    unfold rho
    linarith only [hh]
  have he0 := (tendsto_order.1 (continuous_t0.tendsto reference)).1 1 ht0
  have he1 := (tendsto_order.1 (continuous_t1.tendsto reference)).1 1 ht1
  have hea := (tendsto_order.1 continuousAt_a_reference).1 (1/8) ha0
  have heb := (tendsto_order.1 continuousAt_a_reference).2 (1/2) ha1
  have hcTq : Continuous (fun x : Shape => totalTime x+q x) := continuous_totalTime.add continuous_q
  have heT := (tendsto_order.1 (hcTq.tendsto reference)).2 6 hTq
  have hen := (tendsto_order.1 continuousAt_normPolynomial_reference).2 64 normPolynomial_reference_lt
  have he : ∀ᶠ x : Shape in 𝓝 reference,
      Regular x ∧ 1 ≤ t0 x ∧ 1 ≤ t1 x ∧ 1/8 ≤ a x ∧ a x ≤ 1/2 ∧
      totalTime x+q x ≤ 6 ∧ ‖source x‖^2 ≤ 64 := by
    filter_upwards [eventually_regular_reference,he0,he1,hea,heb,heT,hen]
      with x R h0 h1 ha hb hT hn
    exact ⟨R,h0.le,h1.le,ha.le,hb.le,hT.le,(normPolynomial_eq R ▸ hn.le)⟩
  obtain ⟨d,hd,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨d/2,half_pos hd,fun x hx => hball ?_⟩
  have hh : dist x reference ≤ d/2 := (dist_pi_le_iff (half_pos hd).le).mpr
    (fun i => by simpa only [Real.dist_eq] using hx i)
  exact hh.trans_lt (by linarith only [hd])

end
end StrongSilver.FourPhase
