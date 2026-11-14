-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.MoreauSmooth
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace StrongSilver.Moreau
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Potential (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  value : E → ENNReal
  lowerSemicontinuous : LowerSemicontinuous value
  zero : value 0 = 0
  convex : ∀ x y : E, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
    value (a • x+b • y) ≤ ENNReal.ofReal a * value x + ENNReal.ofReal b * value y

def Potential.epigraph (P : Potential E) : Epigraph E where
  carrier := {p | 0 ≤ p.2 ∧ P.value p.1 ≤ ENNReal.ofReal p.2}
  closed := by
    have hc : Continuous (fun p : E × ℝ => (p.1,ENNReal.ofReal p.2)) :=
      continuous_fst.prodMk (ENNReal.continuous_ofReal.comp continuous_snd)
    exact (isClosed_le continuous_const continuous_snd).inter
      (P.lowerSemicontinuous.isClosed_epigraph.preimage hc)
  convex := by
    intro p hp q hq a b ha hb hab
    change 0 ≤ a*p.2+b*q.2 ∧ P.value (a • p.1+b • q.1) ≤ ENNReal.ofReal (a*p.2+b*q.2)
    refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),?_⟩
    calc
      P.value (a • p.1+b • q.1) ≤ ENNReal.ofReal a * P.value p.1 + ENNReal.ofReal b * P.value q.1 :=
        P.convex _ _ _ _ ha hb hab
      _ ≤ ENNReal.ofReal a * ENNReal.ofReal p.2 + ENNReal.ofReal b * ENNReal.ofReal q.2 := by
        gcongr
        · exact hp.2
        · exact hq.2
      _ = ENNReal.ofReal (a*p.2+b*q.2) := by
        rw [ENNReal.ofReal_add (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),
          ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  nonnegative := fun _ h => h.1
  zero_mem := by simp [P.zero]
  upward := by
    intro p hp s hs
    exact ⟨hp.1.trans hs,hp.2.trans (ENNReal.ofReal_le_ofReal hs)⟩

def Potential.Subgradient (P : Potential E) (z g : E) : Prop :=
  P.value z ≠ ⊤ ∧ ∀ w, P.value w ≠ ⊤ →
    (P.value z).toReal + inner ℝ g (w-z) ≤ (P.value w).toReal

theorem epigraph_finite (P : Potential E) (p : E × ℝ) (hp : p ∈ P.epigraph.carrier) :
    P.value p.1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp.2

theorem potential_graph_mem (P : Potential E) (z : E) (hz : P.value z ≠ ⊤) :
    (z,(P.value z).toReal) ∈ P.epigraph.carrier := by
  exact ⟨ENNReal.toReal_nonneg, by rw [ENNReal.ofReal_toReal hz]⟩

theorem supported_height (P : Potential E) (z g : E) (t : ℝ)
    (h : Supports P.epigraph z t g) : t = (P.value z).toReal := by
  have hz := epigraph_finite P (z,t) h.1
  have h1 := ENNReal.toReal_le_of_le_ofReal h.1.1 h.1.2
  have h2 := h.2 _ (potential_graph_mem P z hz)
  simp only [sub_self, inner_zero_right, add_zero] at h2
  exact le_antisymm h2 h1

theorem subgradient_iff_supports (P : Potential E) (z g : E) :
    P.Subgradient z g ↔ Supports P.epigraph z (P.value z).toReal g := by
  constructor
  · intro h
    refine ⟨potential_graph_mem P z h.1,fun q hq => ?_⟩
    exact (h.2 q.1 (epigraph_finite P q hq)).trans
      (ENNReal.toReal_le_of_le_ofReal hq.1 hq.2)
  · intro h
    exact ⟨epigraph_finite P _ h.1,fun w hw => h.2 _ (potential_graph_mem P w hw)⟩

variable [ProperSpace E]

theorem proximal_height (P : Potential E) (x : E) :
    (minimizingPair P.epigraph x).2 = (P.value (proximal P.epigraph x)).toReal :=
  supported_height P _ _ _ (minimizingPair_supports P.epigraph x)

theorem proximal_subgradient (P : Potential E) (x : E) :
    P.Subgradient (proximal P.epigraph x) (gradient P.epigraph x) := by
  rw [subgradient_iff_supports, ← proximal_height P x]
  exact minimizingPair_supports P.epigraph x

theorem proximal_iff_subgradient (P : Potential E) (x z : E) :
    proximal P.epigraph x = z ↔ P.Subgradient z (x-z) := by
  constructor
  · intro h
    simpa only [gradient,h] using proximal_subgradient P x
  · intro h
    have he := minimizingPair_eq_of_supports P.epigraph x z (P.value z).toReal
      ((subgradient_iff_supports P z (x-z)).mp h)
    exact congrArg Prod.fst he

theorem extended_envelope_value (P : Potential E) (x : E) :
    envelope P.epigraph x = (P.value (proximal P.epigraph x)).toReal +
      ‖x-proximal P.epigraph x‖^2/2 := by
  unfold envelope objective
  rw [proximal_height]
  rfl

theorem extended_envelope_minimum (P : Potential E) (x : E) :
    ∃! z : E, P.value z ≠ ⊤ ∧
      envelope P.epigraph x = (P.value z).toReal + ‖x-z‖^2/2 ∧
      ∀ w, P.value w ≠ ⊤ →
        (P.value z).toReal + ‖x-z‖^2/2 ≤ (P.value w).toReal + ‖x-w‖^2/2 := by
  refine ⟨proximal P.epigraph x,⟨(proximal_subgradient P x).1,extended_envelope_value P x,?_⟩,?_⟩
  · intro w hw
    rw [← extended_envelope_value]
    exact minimizingPair_min P.epigraph x _ (potential_graph_mem P w hw)
  · intro z hz
    have hm : ∀ q ∈ P.epigraph.carrier,
        objective x (z,(P.value z).toReal) ≤ objective x q := by
      intro q hq
      change (P.value z).toReal+‖x-z‖^2/2 ≤ q.2+‖x-q.1‖^2/2
      exact (hz.2.2 q.1 (epigraph_finite P q hq)).trans
        (add_le_add (ENNReal.toReal_le_of_le_ofReal hq.1 hq.2) le_rfl)
    have he := minimizer_unique P.epigraph x (z,(P.value z).toReal) (minimizingPair P.epigraph x)
      (potential_graph_mem P z hz.1) (minimizingPair_mem P.epigraph x) hm
      (minimizingPair_min P.epigraph x)
    exact congrArg Prod.fst he

theorem extended_envelope_interpolates (P : Potential E) (z g : E) (h : P.Subgradient z g) :
    HasGradientAt (envelope P.epigraph) g (z+g) ∧
    envelope P.epigraph (z+g) = (P.value z).toReal+‖g‖^2/2 := by
  have hi := envelope_interpolates P.epigraph z g (P.value z).toReal
    ((subgradient_iff_supports P z g).mp h)
  refine ⟨?_,hi.2⟩
  have hd := envelope_hasGradientAt P.epigraph (z+g)
  rwa [hi.1] at hd

/-- Equality with the extended-real infimum in the paper's definition. -/
theorem extended_envelope_infimum (P : Potential E) (x : E) :
    ENNReal.ofReal (envelope P.epigraph x) =
      ⨅ z : E, P.value z + ENNReal.ofReal (‖x-z‖^2/2) := by
  have hs (z : E) (hz : P.value z ≠ ⊤) :
      ENNReal.ofReal ((P.value z).toReal+‖x-z‖^2/2) =
        P.value z+ENNReal.ofReal (‖x-z‖^2/2) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hz]
  apply le_antisymm
  · apply le_iInf
    intro z
    by_cases hz : P.value z = ⊤
    · simp [hz]
    · rw [← hs z hz]
      exact ENNReal.ofReal_le_ofReal
        (minimizingPair_min P.epigraph x _ (potential_graph_mem P z hz))
  · calc
      (⨅ z : E, P.value z+ENNReal.ofReal (‖x-z‖^2/2)) ≤
          P.value (proximal P.epigraph x)+ENNReal.ofReal (‖x-proximal P.epigraph x‖^2/2) := iInf_le _ _
      _ = ENNReal.ofReal (envelope P.epigraph x) := by
        rw [← hs _ (proximal_subgradient P x).1, extended_envelope_value]

end
end StrongSilver.Moreau
