-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IntervalInverseOrder

namespace StrongSilver
open Set Filter
open scoped Topology
noncomputable section

theorem intervalGraphInverse_left_inverse {a b θ : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b)) (hθ : θ ∈ Icc a b) :
    intervalGraphInverse hab hc hs (X θ) = θ := by
  have hy : X θ ∈ Icc (X b) (X a) :=
    ⟨hs.antitoneOn hθ ⟨hab,le_rfl⟩ hθ.2,hs.antitoneOn ⟨le_rfl,hab⟩ hθ hθ.1⟩
  exact hs.injOn (intervalGraphInverse_mem hab hc hs _) hθ (intervalGraphInverse_right_inverse hab hc hs hy)

theorem intervalGraphInverse_hasDerivWithinAt {a b y d : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b))
    (hy : y ∈ Icc (X b) (X a))
    (hd : HasDerivWithinAt X d (Icc a b) (intervalGraphInverse hab hc hs y)) (hd0 : d ≠ 0) :
    HasDerivWithinAt (intervalGraphInverse hab hc hs) d⁻¹ (Icc (X b) (X a)) y := by
  let U := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hd0)
  have hXd : HasFDerivWithinAt X (U : ℝ →L[ℝ] ℝ) (Icc a b) (intervalGraphInverse hab hc hs y) := hd
  have htendsto : Tendsto (intervalGraphInverse hab hc hs) (𝓝[Icc (X b) (X a)] y)
      (𝓝[Icc a b] intervalGraphInverse hab hc hs y) :=
    (intervalGraphInverse_continuous hab hc hs).continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun z hz => intervalGraphInverse_mem hab hc hs z)
  have hinverse : ∀ᶠ z in 𝓝[Icc (X b) (X a)] y, X (intervalGraphInverse hab hc hs z) = z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact intervalGraphInverse_right_inverse hab hc hs hz
  exact hXd.of_local_left_inverse htendsto hy hinverse

end
end StrongSilver
