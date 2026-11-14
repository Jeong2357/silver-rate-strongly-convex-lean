-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PositiveTrace
import StrongSilver.InitialQueryBounds
import StrongSilver.InitialGateRatio

namespace StrongSilver.PositiveTrace
noncomputable section
set_option maxHeartbeats 1000000

def ofInitialPath {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {μ κ B r : ℝ} {h : List ℝ} {n : ℕ} (P : SupportedPath V μ n)
    (hs : List.ofFn P.steps = h) (hNZ : P.x 0 ≠ 0) (hp : P.family.PositiveAt (P.x 0))
    (hg : P.family.Gate (P.x 0) (initialGateConstant/(κ/B)^2))
    (hb : ∀ i, |inner ℝ (unitDirection (P.x 0)) (P.family.z i)| ≤ initialPointRelativeConstant*(κ/B)*‖P.x 0‖ ∧
      |inner ℝ (unitDirection (P.x 0)) (P.family.g i)| ≤ initialSlopeRelativeConstant*(κ/B)*‖P.x 0‖/κ)
    (hr : r ≤ ‖P.x (Fin.last n)‖^2/‖P.x 0‖^2) :
    PositiveTrace μ h (initialGateConstant/(κ/B)^2) (initialPointRelativeConstant*(κ/B))
      (initialSlopeRelativeConstant*(κ/B)/κ) r := by
  apply ofPath P hs hNZ hp hg ?_ hr
  intro i
  refine ⟨(hb i).1,(hb i).2.trans_eq ?_⟩
  ring

end
end StrongSilver.PositiveTrace
