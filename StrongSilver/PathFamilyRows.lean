-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PathConcatenation
import StrongSilver.FourPhaseSuffixBounds

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι κ : Type*}
set_option maxHeartbeats 2000000

def SupportFamily.RowOf (F : SupportFamily ι V) (z g : V) (d : ℝ) : Prop :=
  ∃ i, z = F.z i ∧ g = F.g i ∧ d = F.d i

def SupportedPath.WithinFamily {μ : ℝ} {n : ℕ} (P : SupportedPath V μ n) (F : SupportFamily ι V) : Prop :=
  ∀ i, F.RowOf (P.family.z i) (P.family.g i) (P.family.d i)

theorem FourPhaseSuffixBounds.of_rows {F : SupportFamily ι V} {G : SupportFamily κ V}
    {Y : V} {H Z : ℝ} (B : FourPhaseSuffixBounds F Y H Z)
    (hrows : ∀ j, F.RowOf (G.z j) (G.g j) (G.d j)) : FourPhaseSuffixBounds G Y H Z := by
  refine ⟨B.source_nonzero,B.scale_positive,B.offset_nonnegative,?_,?_,?_,?_⟩
  · intro j; obtain ⟨i,hz,hg,hd⟩ := hrows j; rw [hz]; exact B.point_positive i
  · intro j; obtain ⟨i,hz,hg,hd⟩ := hrows j; rw [hg]; exact B.slope_positive i
  · intro j; obtain ⟨i,hz,hg,hd⟩ := hrows j; rw [hg]; exact B.slope_upper i
  · intro j; obtain ⟨i,hz,hg,hd⟩ := hrows j; rw [hz,hd]; exact B.height_lower i

theorem SupportFamily.gate_of_rows (F : SupportFamily ι V) (G : SupportFamily κ V)
    {Y : V} {η : ℝ} (hgate : F.Gate Y η)
    (hrows : ∀ j, F.RowOf (G.z j) (G.g j) (G.d j)) : G.Gate Y η := by
  intro j
  obtain ⟨i,hz,hg,hd⟩ := hrows j
  change G.d j+inner ℝ (G.g j) (η • Y-G.z j) ≤ 0
  rw [hz,hg,hd]
  exact hgate i

variable [ProperSpace V]

theorem SupportedPath.concat_within_family {μ : ℝ} {n m : ℕ}
    (P : SupportedPath V μ n) (Q : SupportedPath V μ m) (F : SupportFamily ι V)
    (hP : P.WithinFamily F) (hQ : Q.WithinFamily F)
    (hjoin : P.x (Fin.last n) = Q.x 0) :
    ∃ J : SupportedPath V μ (List.ofFn P.steps++List.ofFn Q.steps).length,
      J.x 0 = P.x 0 ∧ J.x (Fin.last _) = Q.x (Fin.last m) ∧
      List.ofFn J.steps = List.ofFn P.steps++List.ofFn Q.steps ∧ J.WithinFamily F := by
  have hPQ : ∀ i j, P.family.d i+inner ℝ (P.family.g i) (Q.family.z j-P.family.z i) ≤ Q.family.d j := by
    intro i j
    obtain ⟨a,hza,hga,hda⟩ := hP i
    obtain ⟨b,hzb,hgb,hdb⟩ := hQ j
    rw [hza,hga,hda,hzb,hdb]
    exact F.supports a b
  have hQP : ∀ j i, Q.family.d j+inner ℝ (Q.family.g j) (P.family.z i-Q.family.z j) ≤ P.family.d i := by
    intro j i
    obtain ⟨a,hza,hga,hda⟩ := hP i
    obtain ⟨b,hzb,hgb,hdb⟩ := hQ j
    rw [hgb,hdb,hza,hzb,hda]
    exact F.supports b a
  let J := P.concatenated Q hPQ hQP
  refine ⟨J,rfl,P.concatenated_endpoint Q hPQ hQP hjoin,List.ofFn_get _,?_⟩
  exact P.concatenated_family_inherits Q hPQ hQP hjoin F.RowOf hP hQ

end
end StrongSilver
