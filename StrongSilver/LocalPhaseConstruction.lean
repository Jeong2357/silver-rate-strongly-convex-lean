-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LocalPhaseBounds

namespace StrongSilver
open Set Real Filter Complex
noncomputable section
set_option maxHeartbeats 1000000

structure LocalPhaseCertificate (A μ b T e : ℝ) (h : List ℝ) where
  planar : PlanarBoundaryCertificate A μ
  scalar : ScalarTrajectoryCertificate μ T A b e h
  R : ℂ
  D : ℝ
  D_nonnegative : 0 ≤ D
  b_large : 8 ≤ b
  mu_positive : 0 < μ
  b_lt_T : b < T
  A_lt_T : A < T
  mu_T_lt_one : μ*T < 1
  gap_cap : ∀ c ∈ h, 0 < c → c ≤ A
  small_steps : ∀ c ∈ h, μ*c < 1
  q_positive : 0 < quadraticMultiplier μ h*(1-μ*b)
  planar_run : iterate h planar.physical R = (⟨planarEpsilon A,1⟩ : ℂ)
  planar_states : ∀ j : ℕ, j ≤ h.length → iterate (h.take j) planar.physical R ∈ planar.domain
  pad : (quadraticMultiplier μ h*(1-μ*b))*D^2 = (b-1)*inner ℝ R (⟨planarEpsilon A,1⟩ : ℂ)

namespace LocalPhaseCertificate
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)

def path : SupportedPath PhaseSpace μ (h++[b]).length :=
  localPhasePath L.planar L.scalar.S h b L.R L.D L.scalar.x

theorem start : L.path.x 0 = phasePoint L.R L.D L.scalar.x := rfl

theorem endpoint : L.path.x (Fin.last (h++[b]).length) =
    phasePoint (-(b-1) • (⟨planarEpsilon A,1⟩ : ℂ))
      ((quadraticMultiplier μ h*(1-μ*b))*L.D) 0 :=
  localPhasePath_end L.planar L.scalar.S h b L.R L.D L.scalar.x e
    L.planar_run L.scalar.terminal L.scalar.selected

theorem orthogonal : inner ℝ (L.path.x 0) (L.path.x (Fin.last (h++[b]).length)) = 0 := by
  rw [L.start,L.endpoint,phase_start_endpoint_inner,L.pad]
  ring

theorem endpoint_norm_lower : b-1 ≤ ‖L.path.x (Fin.last (h++[b]).length)‖ := by
  rw [L.endpoint]
  exact phase_endpoint_norm_lower (by linarith [L.b_large])

theorem endpoint_ne_zero : L.path.x (Fin.last (h++[b]).length) ≠ 0 := by
  intro he
  have hh := L.endpoint_norm_lower
  rw [he,norm_zero] at hh
  linarith [L.b_large]

theorem positive_at_source : L.path.family.PositiveAt (L.path.x 0) :=
  localPhase_source_positive L.planar L.scalar.S h b L.R L.D L.scalar.x L.D_nonnegative
    L.small_steps L.planar_states L.scalar.positive

theorem endpoint_slopes_nonpositive (i : Fin (h++[b]).length) :
    inner ℝ (L.path.x (Fin.last (h++[b]).length)) (L.path.family.g i) ≤ 0 := by
  rw [L.endpoint]
  exact localPhase_endpoint_slope_nonpositive L.planar L.scalar.S h b L.R L.D L.scalar.x
    (quadraticMultiplier μ h*(1-μ*b)) (by linarith [L.b_large]) i

theorem height_floor (i : Fin (h++[b]).length) :
    ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2 ≤ L.path.family.d i := by
  apply localPhase_height_floor L.planar L.scalar.S h b L.R L.D L.scalar.x _ _ i
  intro j hj
  exact (L.scalar.estimates j hj).2.2.2.2

end LocalPhaseCertificate

/-- Both analytic constructions and the orthogonal padding coordinate exist
simultaneously for each sufficiently large working scale. -/
theorem eventually_exists_local_phase : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e : ℝ, 0 < μ → μ*A ≤ 1 → 8 ≤ b → b < T → A < T →
      0 < e → μ*T < 1 → ∀ h : List ℝ, (∀ c ∈ h, 0 < c → c ≤ A) →
      Nonempty (LocalPhaseCertificate A μ b T e h) := by
  filter_upwards [eventually_exists_planar_boundary_certificate] with A hex
  intro μ b T e hμ hμA hb hbT hAT he hμT h hh
  have hT : 0 < T := (show (0 : ℝ) < b by linarith).trans hbT
  have hμb : μ*b < 1 := (mul_lt_mul_of_pos_left hbT hμ).trans hμT
  have hsmall : ∀ c ∈ h, μ*c < 1 := by
    intro c hc
    by_cases hcp : 0 < c
    · exact (mul_le_mul_of_nonneg_left (hh c hc hcp) hμ.le).trans_lt
        ((mul_lt_mul_of_pos_left hAT hμ).trans hμT)
    · have hm := mul_nonpos_of_nonneg_of_nonpos hμ.le (le_of_not_gt hcp)
      linarith only [hm]
  obtain ⟨C⟩ := hex μ hμ.le hμA
  obtain ⟨S⟩ := exists_scalar_trajectory_certificate hb hbT hAT he hμ.le hμT h hh
  obtain ⟨R,hR,hrun,hstates⟩ := C.terminal_trajectory_exists h (fun c hc => by linarith [hsmall c hc])
  have hJ : 0 ≤ inner ℝ R (⟨planarEpsilon A,1⟩ : ℂ) :=
    complex_inner_nonnegative hR.1 hR.2.1 C.epsilon_pos.le zero_le_one
  have hq : 0 < quadraticMultiplier μ h*(1-μ*b) :=
    mul_pos (quadraticMultiplier_positive h hsmall) (by linarith)
  obtain ⟨D,hD,hpad⟩ := exists_orthogonal_phase_pad hJ hq (by linarith : 1 ≤ b)
  exact ⟨{
    planar := C
    scalar := S
    R := R
    D := D
    D_nonnegative := hD
    b_large := hb
    mu_positive := hμ
    b_lt_T := hbT
    A_lt_T := hAT
    mu_T_lt_one := hμT
    gap_cap := hh
    small_steps := hsmall
    q_positive := hq
    planar_run := hrun
    planar_states := hstates
    pad := hpad
  }⟩

end
end StrongSilver
