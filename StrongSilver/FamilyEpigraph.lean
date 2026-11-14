-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportTransport
import StrongSilver.ExactProximalValues

namespace StrongSilver.SupportFamily
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1000000

def rows (F : SupportFamily ι V) : List (V × ℝ) := List.ofFn (fun i : Fin (Fintype.card ι) =>
  let j := (Fintype.equivFin ι).symm i
  (F.g j,inner ℝ (F.g j) (F.z j)-F.d j))

theorem rows_nonnegative (F : SupportFamily ι V) : ∀ r ∈ F.rows, 0 ≤ r.2 := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  exact sub_nonneg.mpr (F.origin _)

theorem row_mem (F : SupportFamily ι V) (i : ι) : (F.g i,inner ℝ (F.g i) (F.z i)-F.d i) ∈ F.rows := by
  apply List.mem_ofFn.mpr
  refine ⟨(Fintype.equivFin ι) i,?_⟩
  simp only [Equiv.symm_apply_apply]

def epigraph (F : SupportFamily ι V) : Moreau.Epigraph V := Moreau.planeEpigraph F.rows F.rows_nonnegative
def potential (F : SupportFamily ι V) : V → ℝ := Moreau.planeMaximum F.rows

theorem row_upper (F : SupportFamily ι V) (i : ι) : ∀ r ∈ F.rows, inner ℝ r.1 (F.z i)-r.2 ≤ F.d i := by
  intro r hr
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
  have hh := F.supports ((Fintype.equivFin ι).symm j) i
  rw [inner_sub_right] at hh
  dsimp only
  linarith only [hh]

theorem epigraph_supports (F : SupportFamily ι V) (i : ι) : Moreau.Supports F.epigraph (F.z i) (F.d i) (F.g i) :=
  Moreau.active_plane_supports F.rows F.rows_nonnegative (F.z i) (F.g i) (F.d i)
    (F.nonnegative i) (F.row_mem i) (F.row_upper i)

theorem potential_at_point (F : SupportFamily ι V) (i : ι) : F.potential (F.z i) = F.d i :=
  Moreau.active_plane_value F.rows (F.z i) (F.g i) (F.d i) (F.nonnegative i) (F.row_mem i) (F.row_upper i)

theorem potential_zero_of_gate (F : SupportFamily ι V) {Y : V} {η t : ℝ}
    (hpositive : ∀ i, 0 ≤ inner ℝ Y (F.g i)) (hgate : F.Gate Y η) (ht : t ≤ η) :
    F.potential (t • Y) = 0 := by
  apply le_antisymm _ (Moreau.planeMaximum_nonnegative _ _)
  apply (Moreau.planeMaximum_le _ _ _).mpr
  refine ⟨le_rfl,fun r hr => ?_⟩
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  have hh := F.gate_below hpositive hgate ht ((Fintype.equivFin ι).symm i)
  rw [inner_sub_right] at hh
  dsimp only
  linarith only [hh]

variable [ProperSpace V]

theorem epigraph_interpolates (F : SupportFamily ι V) (i : ι) :
    Moreau.gradient F.epigraph (F.z i+F.g i) = F.g i ∧
    Moreau.minimizingPair F.epigraph (F.z i+F.g i) = (F.z i,F.d i) :=
  ⟨(Moreau.envelope_interpolates F.epigraph (F.z i) (F.g i) (F.d i) (F.epigraph_supports i)).1,
    Moreau.minimizingPair_eq_from_supports F.epigraph (F.z i) (F.g i) (F.d i) (F.epigraph_supports i)⟩

end
end StrongSilver.SupportFamily
