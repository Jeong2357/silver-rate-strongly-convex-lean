-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.RunSupportedPath
import StrongSilver.AffinePhases

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι κ : Type*}
set_option maxHeartbeats 1600000

def SupportFamily.reindex (F : SupportFamily ι V) (e : κ → ι) : SupportFamily κ V where
  z := F.z ∘ e
  g := F.g ∘ e
  d := F.d ∘ e
  nonnegative := fun i => F.nonnegative (e i)
  origin := fun i => F.origin (e i)
  supports := fun i j => F.supports (e i) (e j)

/-- Actual affine GD updates with supporting data taken from one common
finite family. This permits later gluing of phases using the already
proved mutual support comparisons. -/
def affineSupportPath (F : SupportFamily ι V) (μ : ℝ) (g a : V) (h : List ℝ)
    (e : Fin h.length → ι) (hg : ∀ i, F.g (e i) = g)
    (hz : ∀ i : Fin h.length, F.z (e i)+F.g (e i) =
      iterate (h.take i.val) (fun y => μ • y+(1-μ) • g) a) :
    SupportedPath V μ h.length where
  x := fun i => iterate (h.take i.val) (fun y => μ • y+(1-μ) • g) a
  family := F.reindex e
  steps := fun i => h.get i
  split := fun i => (hz i).symm
  update := by
    intro i
    change iterate (h.take (i.val+1)) _ a = _
    rw [iterate_prefix_succ]
    change _ = _-h.get i • (μ • _+(1-μ) • F.g (e i))
    rw [hg]
    rfl

theorem affineSupportPath_start (F : SupportFamily ι V) (μ : ℝ) (g a : V) (h : List ℝ)
    (e : Fin h.length → ι) (hg : ∀ i, F.g (e i) = g)
    (hz : ∀ i : Fin h.length, F.z (e i)+F.g (e i) =
      iterate (h.take i.val) (fun y => μ • y+(1-μ) • g) a) :
    (affineSupportPath F μ g a h e hg hz).x 0 = a := rfl

theorem affineSupportPath_end (F : SupportFamily ι V) {μ : ℝ} (hμ : μ ≠ 0)
    (g a : V) (h : List ℝ) (e : Fin h.length → ι) (hg : ∀ i, F.g (e i) = g)
    (hz : ∀ i : Fin h.length, F.z (e i)+F.g (e i) =
      iterate (h.take i.val) (fun y => μ • y+(1-μ) • g) a) :
    (affineSupportPath F μ g a h e hg hz).x (Fin.last h.length) =
      quadraticMultiplier μ h • a-(((1-μ)/μ)*(1-quadraticMultiplier μ h)) • g := by
  change iterate (h.take h.length) _ a = _
  rw [List.take_length,affine_phase_formula hμ]

end
end StrongSilver
