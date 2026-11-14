-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarRampUniform

namespace StrongSilver
open Set Real
noncomputable section
set_option maxHeartbeats 1000000

def ScalarContraction.physical (S : ScalarContraction) (μ : ℝ) : ℝ → ℝ :=
  stronglyConvexGradient μ (Moreau.gradient S.epigraph)

/-- Concrete scalar data for Lemma 3.4; existence is proved below. -/
structure ScalarTrajectoryCertificate (μ T A b e : ℝ) (h : List ℝ) where
  S : ScalarContraction
  x : ℝ
  terminal : iterate h (S.physical μ) x = e
  selected : e-b*S.physical μ e = 0
  positive : ∀ i : ℕ, i ≤ h.length → 0 < iterate (h.take i) (S.physical μ) x
  estimates : ∀ i : ℕ, i ≤ h.length →
    let t := iterate (h.take i) (S.physical μ) x
    (e/2)*Real.exp (-negativeLogSum h T) ≤ t ∧
    t ≤ scalarRampGrowth T A b h*e ∧
    0 ≤ S.g t ∧ S.g t ≤ 2*(scalarRampGrowth T A b h/T+1/b)*e ∧
    ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2 ≤ S.potential (S.proximalMap t)

/-- Scalar-ramp existence, including exact GD and all the signed-state and height
estimates. The constants in (3.14) are explicit. -/
theorem exists_scalar_trajectory_certificate {μ T A b e : ℝ} (hb : 8 ≤ b) (hbT : b < T)
    (hAT : A < T) (he : 0 < e) (hμ0 : 0 ≤ μ) (hμT : μ*T < 1)
    (h : List ℝ) (hh : ∀ c ∈ h, 0 < c → c ≤ A) :
    Nonempty (ScalarTrajectoryCertificate μ T A b e h) := by
  have hb0 : 0 < b := by linarith
  have hT : 0 < T := hb0.trans hbT
  obtain ⟨R,hbase,ha,hv,hve,hsel⟩ := exists_selected_scalar_ramp hb hbT he
  have hμbase : μ ≤ R.base := by
    rw [hbase]
    exact ((lt_div_iff₀ hT).mpr (by nlinarith only [hμT])).le
  have hbasehalf : R.base ≤ 1/8 := by
    rw [hbase]
    exact (one_div_le_one_div hT (show (0 : ℝ) < 8 by norm_num)).mpr (by linarith)
  have hμ1 : μ < 1 := by linarith only [hμbase,hbasehalf]
  have hμhalf : μ ≤ 1/2 := by linarith only [hμbase,hbasehalf]
  let S := R.contraction hμ0 hμ1 hμbase
  have hG : S.physical μ = R.physical := funext (fun t => R.actual_physical_gradient hμ0 hμ1 hμbase t)
  have hall : ∀ c ∈ h, R.base*c < 1 := by
    intro c hc
    rw [hbase]
    by_cases hcp : 0 < c
    · have hcT := (hh c hc hcp).trans_lt hAT
      have ht := (div_lt_one hT).mpr hcT
      simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using ht
    · have hm := mul_nonpos_of_nonneg_of_nonpos (one_div_pos.mpr hT).le (le_of_not_gt hcp)
      linarith only [hm]
  obtain ⟨x,hrun,hstates⟩ := R.positive_trajectory h hall he
  have haU : R.amplitude ≤ e/b := by
    rw [ha]
    have hm := mul_nonneg (one_div_pos.mpr hT).le he.le
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm]
  refine ⟨{
    S := S
    x := x
    terminal := by rw [hG]; exact hrun
    selected := by rw [hG]; exact scalar_ramp_selected_step hsel hb0.ne'
    positive := by rw [hG]; exact hstates
    estimates := ?_
  }⟩
  intro i hi
  rw [hG]
  exact R.uniform_state_estimates hT hb0 he hAT hbase haU hv hve hμ0 hμ1 hμbase hμhalf
    h hh x hrun hstates i hi

end
end StrongSilver
