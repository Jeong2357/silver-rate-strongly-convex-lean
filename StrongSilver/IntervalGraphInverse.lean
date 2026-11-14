-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Inverse

namespace StrongSilver
open Set Filter
open scoped Topology
noncomputable section

theorem exists_antitone_interval_homeomorph {a b : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b)) :
    ∃ H : Icc a b ≃ₜ Icc (X b) (X a), ∀ t : Icc a b, (H t : ℝ) = X t := by
  let f : Icc a b → Icc (X b) (X a) := fun t =>
    ⟨X t,hs.antitoneOn t.property ⟨hab,le_rfl⟩ t.property.2,
      hs.antitoneOn ⟨le_rfl,hab⟩ t.property t.property.1⟩
  have hcf : Continuous f := hc.restrict.subtype_mk _
  have hinj : Function.Injective f := by
    intro t u htu
    apply Subtype.ext
    exact hs.injOn t.property u.property (congrArg Subtype.val htu)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : ℝ) ∈ X '' Icc a b := by
      rw [ContinuousOn.image_Icc_of_antitoneOn hab hc hs.antitoneOn]
      exact y.property
    obtain ⟨t,ht,he⟩ := hy
    exact ⟨⟨t,ht⟩,Subtype.ext he⟩
  let E := Equiv.ofBijective f ⟨hinj,hsurj⟩
  exact ⟨E.toHomeomorphOfContinuousClosed hcf hcf.isClosedMap,fun t => rfl⟩

def antitoneIntervalHomeomorph {a b : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b)) : Icc a b ≃ₜ Icc (X b) (X a) :=
  (exists_antitone_interval_homeomorph hab hc hs).choose

theorem antitoneIntervalHomeomorph_apply {a b : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b)) (t : Icc a b) :
    (antitoneIntervalHomeomorph hab hc hs t : ℝ) = X t :=
  (exists_antitone_interval_homeomorph hab hc hs).choose_spec t

def intervalGraphInverse {a b : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b)) (y : ℝ) : ℝ :=
  ((antitoneIntervalHomeomorph hab hc hs).symm
    (projIcc (X b) (X a) (hs.antitoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab) y) : ℝ)

theorem intervalGraphInverse_continuous {a b : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b)) :
    Continuous (intervalGraphInverse hab hc hs) :=
  continuous_subtype_val.comp ((antitoneIntervalHomeomorph hab hc hs).symm.continuous.comp
    (LipschitzWith.projIcc _).continuous)

theorem intervalGraphInverse_mem {a b : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b)) (y : ℝ) :
    intervalGraphInverse hab hc hs y ∈ Icc a b :=
  ((antitoneIntervalHomeomorph hab hc hs).symm
    (projIcc (X b) (X a) (hs.antitoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab) y)).property

theorem intervalGraphInverse_right_inverse {a b : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b)) {y : ℝ}
    (hy : y ∈ Icc (X b) (X a)) : X (intervalGraphInverse hab hc hs y) = y := by
  let H := antitoneIntervalHomeomorph hab hc hs
  have hh := congrArg Subtype.val (H.apply_symm_apply ⟨y,hy⟩)
  rw [antitoneIntervalHomeomorph_apply] at hh
  have hord : X b ≤ X a := hs.antitoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  simpa only [intervalGraphInverse,projIcc_of_mem hord hy] using hh

theorem intervalGraphInverse_hasDerivAt {a b y d : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b))
    (hy : y ∈ Ioo (X b) (X a))
    (hd : HasDerivAt X d (intervalGraphInverse hab hc hs y)) (hd0 : d ≠ 0) :
    HasDerivAt (intervalGraphInverse hab hc hs) d⁻¹ y := by
  apply HasDerivAt.of_local_left_inverse (intervalGraphInverse_continuous hab hc hs).continuousAt hd hd0
  filter_upwards [Icc_mem_nhds hy.1 hy.2] with z hz
  exact intervalGraphInverse_right_inverse hab hc hs hz

end
end StrongSilver
