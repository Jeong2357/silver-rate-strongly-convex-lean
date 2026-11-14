-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteFilteredSums
import Mathlib.Data.List.Perm.Subperm

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3200000

theorem list_nonnegative_subperm_sum_le {α : Type*} (F : α → ℝ) {xs ys : List α}
    (hSub : xs.Subperm ys) (hF : ∀ y ∈ ys, 0 ≤ F y) : (xs.map F).sum ≤ (ys.map F).sum := by
  obtain ⟨zs,hPerm,hList⟩ := List.subperm_iff.mp hSub
  have hh := (hList.map F).sum_le_sum (by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    exact hF z (hPerm.subset hz))
  rwa [(hPerm.map F).sum_eq] at hh

end
end StrongSilver
