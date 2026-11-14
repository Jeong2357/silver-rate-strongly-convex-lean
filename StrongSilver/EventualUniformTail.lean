-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Basic

namespace StrongSilver
open Filter

theorem eventually_all_larger {P : ℝ → Prop} (hP : ∀ᶠ A : ℝ in atTop, P A) :
    ∀ᶠ A : ℝ in atTop, ∀ B : ℝ, A ≤ B → P B := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp hP
  exact eventually_atTop.mpr ⟨A,fun B hB C hBC => hA C (hB.trans hBC)⟩

end StrongSilver
