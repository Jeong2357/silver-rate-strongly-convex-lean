-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialSourceBounds
import StrongSilver.PhaseNormComponents
import StrongSilver.AttachmentRelativeBounds
import StrongSilver.SupportedPathError

namespace StrongSilver
open Real
noncomputable section

def initialQueryConstant : ℝ := 2*initialPlaneConstant+Real.exp 2*initialQuadraticConstant
def initialPointRelativeConstant : ℝ := initialQueryConstant*initialScalarStartConstant
def initialSlopeRelativeConstant : ℝ := (2+initialScalarSlopeConstant)*initialScalarStartConstant

theorem initialQueryConstant_positive : 0 < initialQueryConstant := by
  have := initialPlaneConstant_positive
  have := initialQuadraticConstant_positive
  unfold initialQueryConstant
  positivity
theorem initialPointRelativeConstant_positive : 0 < initialPointRelativeConstant := by
  unfold initialPointRelativeConstant
  exact mul_pos initialQueryConstant_positive initialScalarStartConstant_positive
theorem initialSlopeRelativeConstant_positive : 0 < initialSlopeRelativeConstant := by
  have := initialScalarSlopeConstant_positive
  have := initialScalarStartConstant_positive
  unfold initialSlopeRelativeConstant
  positivity

namespace InitialPhaseBudget
variable {A μ b T κ B e : ℝ} {h : List ℝ} (W : InitialPhaseBudget A μ b T κ B h)
    (L : LocalPhaseCertificate A μ b T e h)
include W L
set_option maxHeartbeats 2400000

theorem relative_queries (heκ : κ ≤ e) (i : Fin (h++[b]).length) :
    ‖L.path.family.z i‖ ≤ initialPointRelativeConstant*(κ/B)*‖L.path.x 0‖ ∧
    ‖L.path.family.g i‖ ≤ initialSlopeRelativeConstant*(κ/B)*‖L.path.x 0‖/κ := by
  let K := κ/B
  have hK : 0 < K := div_pos W.kappa_positive W.B_positive
  have heKe : e ≤ K*e := by
    have hh := mul_le_mul_of_nonneg_right W.ratio_ge_one L.e_positive.le
    simpa only [one_mul] using hh
  have hκKe : κ ≤ K*e := heκ.trans heKe
  have hi : i.val ≤ h.length := by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega
  let Ri := iterate (h.take i.val) L.planar.physical L.R
  let ai := iterate (h.take i.val) (L.scalar.S.physical μ) L.scalar.x
  let c := quadraticMultiplier μ (h.take i.val)
  have hc : 0 < c := quadraticMultiplier_positive _ (fun t ht => L.small_steps t (List.mem_of_mem_take ht))
  have hcU : c ≤ Real.exp 2 := (prefixMultiplier_le_negative_exp L.mu_positive.le L.T_positive L.mu_le_inverse_T h L.small_steps i.val).trans
    (Real.exp_le_exp.mpr W.negative_charge)
  have hscalar := L.scalar.estimates i.val hi
  have hai : 0 < ai := L.scalar.positive i.val hi
  have haiU : ai ≤ initialPlaneConstant*K*e := hscalar.2.1.trans
    (mul_le_mul_of_nonneg_right (W.scalar_growth L) L.e_positive.le)
  have hzscalar := L.scalar.S.proximal_positive_bounds hai.le
  have hzabs : |L.scalar.S.proximalMap ai| ≤ initialPlaneConstant*K*e := by
    rw [abs_of_nonneg (by linarith only [hzscalar.1,hai] : 0 ≤ L.scalar.S.proximalMap ai)]
    exact hzscalar.2.trans haiU
  have hprox : ‖Ri-L.planar.body.projection Ri‖ ≤ initialPlaneConstant*κ := by
    have hh := Moreau.proximal_norm_le L.planar.body.supportEpigraph Ri
    unfold Moreau.proximal at hh
    rw [L.planar.body.exact_proximal_values] at hh
    exact hh.trans (W.planar_all_norm L i.val)
  have hquad : |c*L.D| ≤ (Real.exp 2*initialQuadraticConstant)*κ := by
    rw [abs_of_nonneg (mul_nonneg hc.le L.D_nonnegative)]
    have hh := mul_le_mul hcU (W.quadratic_pad L) L.D_nonnegative (Real.exp_pos 2).le
    nlinarith only [hh]
  have hCp := initialPlaneConstant_positive
  have hCd := initialQuadraticConstant_positive
  have hplaneK := mul_le_mul_of_nonneg_left hκKe hCp.le
  have hquadK := mul_le_mul_of_nonneg_left hκKe (mul_nonneg (Real.exp_pos 2).le hCd.le)
  have hzraw : ‖L.path.family.z i‖ ≤ initialQueryConstant*K*e := by
    have hh := phase_norm_le_sum (Ri-L.planar.body.projection Ri) (c*L.D) (L.scalar.S.proximalMap ai)
    have hb : ‖phasePoint (Ri-L.planar.body.projection Ri) (c*L.D) (L.scalar.S.proximalMap ai)‖ ≤ initialQueryConstant*K*e := by
      unfold initialQueryConstant
      nlinarith only [hh,hprox,hquad,hzabs,hplaneK,hquadK]
    change ‖(localPhasePath L.planar L.scalar.S h b L.R L.D L.scalar.x).family.z i‖ ≤ _
    rw [localPhasePath_proximal,before_selected_take]
    exact hb
  have hgnonneg : 0 ≤ L.scalar.S.g ai := hscalar.2.2.1
  have hgscalar : L.scalar.S.g ai ≤ initialScalarSlopeConstant*K*e/κ :=
    hscalar.2.2.2.1.trans (W.scalar_slope_cap L)
  have hbody := L.planar.body_norm_bound (L.planar.body.projection_mem Ri)
  have hr0 : planarRadius A 0 ≤ 2 := by linarith [L.planar.head_radius_bound,L.planar.scale_le]
  have hgraw : ‖L.path.family.g i‖ ≤ (2+initialScalarSlopeConstant)*K*e/κ := by
    have hh := phase_norm_le_sum (L.planar.body.projection Ri) 0 (L.scalar.S.g ai)
    rw [abs_zero,abs_of_nonneg hgnonneg] at hh
    have htwo : 2 ≤ 2*K*e/κ := (le_div_iff₀ W.kappa_positive).mpr (by nlinarith only [hκKe])
    have hb : ‖phaseSlope (L.planar.body.projection Ri) (L.scalar.S.g ai)‖ ≤ (2+initialScalarSlopeConstant)*K*e/κ := by
      have hbase : ‖phasePoint (L.planar.body.projection Ri) 0 (L.scalar.S.g ai)‖ ≤ 2+initialScalarSlopeConstant*K*e/κ := by
        linarith only [hh,hbody,hr0,hgscalar]
      calc
        _ ≤ 2+initialScalarSlopeConstant*K*e/κ := hbase
        _ ≤ 2*K*e/κ+initialScalarSlopeConstant*K*e/κ := add_le_add htwo le_rfl
        _ = _ := by ring
    change ‖(localPhasePath L.planar L.scalar.S h b L.R L.D L.scalar.x).family.g i‖ ≤ _
    rw [localPhasePath_slope,before_selected_take]
    exact hb
  have hsource : e/initialScalarStartConstant ≤ ‖L.path.x 0‖ := by
    rw [L.start]
    exact (W.scalar_start_lower L).trans (phase_scalar_le_norm _ _ _)
  have heN := (div_le_iff₀ initialScalarStartConstant_positive).mp hsource
  constructor
  · have hh := mul_le_mul_of_nonneg_left heN (mul_nonneg initialQueryConstant_positive.le hK.le)
    have hb := hzraw.trans hh
    unfold initialPointRelativeConstant
    nlinarith only [hb]
  · have hh := mul_le_mul_of_nonneg_left heN
      (div_nonneg (mul_nonneg (by have := initialScalarSlopeConstant_positive; positivity : 0 ≤ 2+initialScalarSlopeConstant) hK.le) W.kappa_positive.le)
    have heq : ((2+initialScalarSlopeConstant)*K/κ)*(‖L.path.x 0‖*initialScalarStartConstant) =
        initialSlopeRelativeConstant*K*‖L.path.x 0‖/κ := by unfold initialSlopeRelativeConstant; ring
    have hrawEq : ((2+initialScalarSlopeConstant)*K/κ)*e = (2+initialScalarSlopeConstant)*K*e/κ := by ring
    rw [heq,hrawEq] at hh
    exact hgraw.trans hh

theorem attachment_queries {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι τ : Type*}
    (F : SupportFamily ι V) (J : SupportFamily τ (AttachmentSpace V PhaseSpace)) {Y : V} {d : ℝ}
    (hY : Y ≠ 0) (heκ : κ ≤ e)
    (horigin : ∀ k, AttachmentOrigin L.path.family F (L.path.x (Fin.last _)) Y d
      (J.z k) (J.g k) (J.d k)) (k : τ) :
    |inner ℝ (unitDirection (alignedAttachment (L.path.x (Fin.last _)) Y (L.path.x 0))) (J.z k)| ≤
      initialPointRelativeConstant*(κ/B)*‖alignedAttachment (L.path.x (Fin.last _)) Y (L.path.x 0)‖ ∧
    |inner ℝ (unitDirection (alignedAttachment (L.path.x (Fin.last _)) Y (L.path.x 0))) (J.g k)| ≤
      initialSlopeRelativeConstant*(κ/B)*‖alignedAttachment (L.path.x (Fin.last _)) Y (L.path.x 0)‖/κ := by
  have hK : 0 ≤ κ/B := (div_pos W.kappa_positive W.B_positive).le
  have hBz : 0 ≤ initialPointRelativeConstant*(κ/B) := mul_nonneg initialPointRelativeConstant_positive.le hK
  have hBg : 0 ≤ initialSlopeRelativeConstant*(κ/B)/κ :=
    div_nonneg (mul_nonneg initialSlopeRelativeConstant_positive.le hK) W.kappa_positive.le
  have hlocal (i : Fin (h++[b]).length) :
      ‖L.path.family.z i‖ ≤ (initialPointRelativeConstant*(κ/B))*‖L.path.x 0‖ ∧
      ‖L.path.family.g i‖ ≤ (initialSlopeRelativeConstant*(κ/B)/κ)*‖L.path.x 0‖ := by
    have hh := W.relative_queries L heκ i
    refine ⟨hh.1,hh.2.trans_eq ?_⟩
    ring
  have hh := attachment_relative_bounds_pair L.path.family F J L.endpoint_ne_zero hY
    (L.path.source_ne_zero L.endpoint_ne_zero) L.orthogonal hBz hBg hlocal horigin k
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  ring

end InitialPhaseBudget
end
end StrongSilver
