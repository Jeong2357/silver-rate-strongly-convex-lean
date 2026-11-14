-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseNewAtRetained
import StrongSilver.FourPhaseRetainedAtNew
import StrongSilver.FourPhaseOrthogonalSum
import StrongSilver.SupportSourceBounds

namespace StrongSilver.FourPhase
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι κ : Type*}
set_option maxHeartbeats 3000000

/-- Gluing the explicit local planes to retained data preserves all
recorded values and slopes, the zero-offset source inequalities, and
the new source gate. The remaining scalar query budget is explicit. -/
theorem attach_four_phase_families {x : Shape} (R : Regular x)
    {F : SupportFamily ι V} {Y : V} {H Z T K η : ℝ}
    (B : FourPhaseSuffixBounds F Y H Z) (hT : 0 < T) (hK : 0 < K)
    (hz0 : 0 ≤ x 7) (hz : K*Z ≤ x 7) (hslope : 8*H*a x ≤ T*K)
    (L : SupportFamily κ Coordinates) (phase : κ → Fin 4)
    (hgs : ∀ i, L.g i = (1/T) • slope x (phase i))
    (hds : ∀ i, L.d i = planeValue x (phase i) (L.z i)/T)
    (BL : FourPhaseSuffixBounds L (source x) T 0)
    (hgate : L.Gate (source x) η)
    (hbudget : ∀ i, (11*T*K/(10*H))*max (inner ℝ axis (L.z i)) 0 ≤ planeValue x (phase i) (L.z i)) :
    ∃ J : SupportFamily (κ ⊕ ι) (AttachmentSpace V Coordinates),
      FourPhaseSuffixBounds J (axisAttachment Y K (source x)) T 0 ∧
      J.Gate (axisAttachment Y K (source x)) η ∧
      (∀ i, J.z (Sum.inl i) = axisAttachment Y K (L.z i) ∧
        J.g (Sum.inl i) = axisAttachment Y K (L.g i) ∧ J.d (Sum.inl i) = (‖Y‖/K)^2*L.d i) ∧
      (∀ j, J.z (Sum.inr j) = retainedMap (W := Coordinates) (F.z j) ∧
        J.g (Sum.inr j) = retainedMap (W := Coordinates) (F.g j) ∧ J.d (Sum.inr j) = F.d j) := by
  let A := axisAttachment Y K
  let w := (‖Y‖/K)^2
  have hw : 0 < w := sq_pos_of_pos (div_pos (norm_pos_iff.mpr B.source_nonzero) hK)
  have hA : ∀ z g, inner ℝ (A z) (A g) = w*inner ℝ z g := axisAttachment_inner B.source_nonzero K
  let Li := L.transport A w hw.le hA
  let Fi := F.retained (W := Coordinates)
  have hLF : ∀ i j, Li.d i+inner ℝ (Li.g i) (Fi.z j-Li.z i) ≤ Fi.d j := by
    intro i j
    change w*L.d i+inner ℝ (A (L.g i)) (retainedMap (F.z j)-A (L.z i)) ≤ 1*F.d j
    rw [one_mul,hgs,hds]
    exact new_plane_at_retained R B hT hK hz0 hz hslope (phase i) (L.z i) j
  have hFL : ∀ j i, Fi.d j+inner ℝ (Fi.g j) (Li.z i-Fi.z j) ≤ Li.d i := by
    intro j i
    change 1*F.d j+inner ℝ (retainedMap (F.g j)) (A (L.z i)-retainedMap (F.z j)) ≤ w*L.d i
    rw [one_mul,hds]
    exact retained_plane_at_new B hT hK (L.z i) j (hbudget i)
  let J := Li.sum Fi hLF hFL
  have hBL : FourPhaseSuffixBounds Li (A (source x)) T 0 := BL.transport A hw hA
  have hzF : ∀ j, inner ℝ (A (source x)) (Fi.z j) = 0 :=
    fun j => axisAttachment_orthogonal (source_orthogonal_axis R) (F.z j)
  have hgF : ∀ j, inner ℝ (A (source x)) (Fi.g j) = 0 :=
    fun j => axisAttachment_orthogonal (source_orthogonal_axis R) (F.g j)
  have hgL : Li.Gate (A (source x)) η := L.transport_gate A w hw.le hA hgate
  refine ⟨J,hBL.sum_orthogonal hLF hFL hzF hgF,
    Li.sum_gate_orthogonal Fi hLF hFL hgL hgF,fun i => ⟨rfl,rfl,rfl⟩,?_⟩
  intro j
  exact ⟨rfl,rfl,by change 1*F.d j = F.d j; exact one_mul _⟩

end
end StrongSilver.FourPhase
