-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TerminalConeAttachment

namespace StrongSilver
open Real
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 2200000

theorem terminal_connector_bounds {μ c A κ K : ℝ} (hμ : 0 < μ) (hc : 2 ≤ c) (hqc : 1/32 ≤ 1-μ*c)
    (hκ : 0 < κ) (hK : 1 ≤ K) (hκKc : κ ≤ K*c) (hcap : μ*A ≤ 1/2)
    (I t : List ℝ) (hcritical : ∀ b ∈ I, 1-μ*b ≠ 0) (ht : ∀ b ∈ t, 0 < b → b ≤ A)
    {Y : V} (hY : Y ≠ 0) :
    let R := 1200000*K*Real.sqrt (maxPrefixProduct μ t)*‖Y‖*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ)
    ∃ n : ℕ, ∃ Q : SupportedPath (AttachmentSpace V ℂ) μ n,
      Q.x 0 ≠ 0 ∧ ‖Q.x 0‖ ≤ R ∧
      Q.x (Fin.last n) = retainedMap (W := ℂ) (quadraticMultiplier μ t • Y) ∧
      List.ofFn Q.steps = (I++[c])++t ∧
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ R+maxPrefixProduct μ t*‖Y‖) ∧
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ R/κ) ∧
      maxPrefixProduct μ t*Real.exp (-2*μ*Scalar.SignedIntervals.positiveMass t)*‖Y‖ ≤ ‖Q.x (Fin.last n)‖ := by
  let R := 1200000*K*Real.sqrt (maxPrefixProduct μ t)*‖Y‖*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ)
  obtain ⟨C,n,Q,hQ,hN,hend,hsteps,hz,hg,hgain⟩ := terminal_cone_attachment hμ hc hqc hcap I t hcritical ht hY
  have hM := maxPrefixProduct_ge_one μ t
  have hV : 0 < ‖Y‖ := norm_pos_iff.mpr hY
  have hsize := C.terminal_scaled_size hμ.le hc hM hV hK hκKc hqc
  have htrace : C.traceRadius I ≤ R := cone_trace_radius_scaled C hμ.le hκ hsize.1 hsize.2 I
  have hRbase : 1200000*K*Real.sqrt (maxPrefixProduct μ t)*‖Y‖ ≤ R := by
    have he : 1 ≤ Real.exp (inverseCharge μ I) := Real.one_le_exp_iff.mpr (inverseCharge_nonneg μ I)
    have hs : 1 ≤ 1+smallPositiveSum μ I/κ := by have := div_nonneg (smallPositiveSum_nonneg μ I) hκ.le; linarith
    have hh := mul_le_mul he hs (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos _).le
    have hm := Real.sqrt_pos.mpr (zero_lt_one.trans_le hM)
    have hK0 : 0 < K := zero_lt_one.trans_le hK
    have hcoef : 0 ≤ 1200000*K*Real.sqrt (maxPrefixProduct μ t)*‖Y‖ := by positivity
    have hscale := mul_le_mul_of_nonneg_left hh hcoef
    dsimp only [R]
    nlinarith only [hscale]
  have hG : 2*C.a ≤ R/κ := (le_div_iff₀ hκ).mpr (by nlinarith only [hsize.2,hRbase])
  refine ⟨n,Q,hQ,hN.trans htrace,hend,hsteps,?_,?_,hgain⟩
  · intro j
    exact (hz j).trans (add_le_add htrace le_rfl)
  · intro j
    exact (hg j).trans hG

end
end StrongSilver
