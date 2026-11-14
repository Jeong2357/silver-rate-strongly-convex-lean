-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.StrongInterpolation

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Finite supporting data for a nonnegative convex proximal potential. -/
structure SupportFamily (ι : Type*) (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  z : ι → V
  g : ι → V
  d : ι → ℝ
  nonnegative : ∀ i, 0 ≤ d i
  origin : ∀ i, d i ≤ inner ℝ (g i) (z i)
  supports : ∀ i j, d i+inner ℝ (g i) (z j-z i) ≤ d j

namespace SupportFamily
variable {ι κ : Type*}

def shifted (F : SupportFamily ι V) (a : ℝ) (ha : 0 ≤ a) (hfloor : ∀ i, a ≤ F.d i) : SupportFamily ι V where
  z := F.z
  g := F.g
  d := fun i => F.d i-a
  nonnegative := fun i => sub_nonneg.mpr (hfloor i)
  origin := fun i => (sub_le_self _ ha).trans (F.origin i)
  supports := by intro i j; have hh := F.supports i j; linarith only [hh]

def sum (F : SupportFamily ι V) (G : SupportFamily κ V)
    (hFG : ∀ i j, F.d i+inner ℝ (F.g i) (G.z j-F.z i) ≤ G.d j)
    (hGF : ∀ j i, G.d j+inner ℝ (G.g j) (F.z i-G.z j) ≤ F.d i) : SupportFamily (ι ⊕ κ) V where
  z := Sum.elim F.z G.z
  g := Sum.elim F.g G.g
  d := Sum.elim F.d G.d
  nonnegative := by intro i; cases i with | inl i => exact F.nonnegative i | inr j => exact G.nonnegative j
  origin := by intro i; cases i with | inl i => exact F.origin i | inr j => exact G.origin j
  supports := by
    intro i j
    cases i with
    | inl i => cases j with | inl j => exact F.supports i j | inr j => exact hFG i j
    | inr i => cases j with | inl j => exact hGF i j | inr j => exact G.supports i j

/-- Subtracting a common intercept and joining preserves every old support value
and slope. The two cross inequalities are exactly the zero-gate conditions. -/
def glue (F : SupportFamily ι V) (G : SupportFamily κ V) (a : ℝ)
    (ha : 0 ≤ a) (hfloor : ∀ i, a ≤ F.d i)
    (hnew : ∀ i j, F.d i-a+inner ℝ (F.g i) (G.z j-F.z i) ≤ 0)
    (hold : ∀ j i, G.d j+inner ℝ (G.g j) (F.z i-G.z j) ≤ 0) : SupportFamily (ι ⊕ κ) V :=
  (F.shifted a ha hfloor).sum G
    (fun i j => (hnew i j).trans (G.nonnegative j))
    (fun j i => (hold j i).trans (sub_nonneg.mpr (hfloor i)))

variable [Fintype ι] [ProperSpace V]

theorem realize (F : SupportFamily ι V) {ρ μ : ℝ} (hρ : 1 ≤ ρ) (hμ : 1/ρ ≤ μ) (hμ1 : μ ≤ 1) :
    ∃ f : V → ℝ, ∃ H : V → V, Admissible ρ f H ∧ f 0 = 0 ∧ (∀ x, 0 ≤ f x) ∧
    ∀ i, H (F.z i+F.g i) = μ • (F.z i+F.g i)+(1-μ) • F.g i ∧
      f (F.z i+F.g i) = (μ/2)*‖F.z i+F.g i‖^2+(1-μ)*(F.d i+‖F.g i‖^2/2) := by
  let e := (Fintype.equivFin ι).symm
  obtain ⟨f,H,hf,h0,hn,hinterp⟩ := finite_strong_interpolation hρ hμ hμ1 (Fintype.card ι)
    (F.z ∘ e) (F.g ∘ e) (F.d ∘ e) (fun i => F.nonnegative (e i)) (fun i => F.origin (e i))
    (fun i j => F.supports (e i) (e j))
  refine ⟨f,H,hf,h0,hn,fun i => ?_⟩
  simpa only [Function.comp_apply,e,Equiv.symm_apply_apply] using hinterp ((Fintype.equivFin ι) i)

end SupportFamily
end
end StrongSilver
