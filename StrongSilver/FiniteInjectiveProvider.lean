-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteFilteredSums
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 4500000
variable {α β : Type*}

/-- Transfer a nonnegative finite family to a larger candidate list
without identifying or counting any selected occurrence twice. -/
theorem list_injective_sum_le (f : α → β) (g : α → ℝ) (F : β → ℝ) (xs : List α) (ys : List β)
    (hn : (xs.map f).Nodup) (hm : ∀ x ∈ xs, f x ∈ ys)
    (hF : ∀ y ∈ ys, 0 ≤ F y) (he : ∀ x ∈ xs, F (f x) = g x) :
    (xs.map g).sum ≤ (ys.map F).sum := by
  have hs : xs.map f ⊆ ys := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact hm x hx
  obtain ⟨zs,hperm,hsub⟩ := List.subperm_iff.mp (hn.subperm hs)
  have hb := (hsub.map F).sum_le_sum (by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
    exact hF y (hperm.subset hy))
  rw [(hperm.map F).sum_eq] at hb
  have heq : (xs.map f).map F = xs.map g := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact he x hx
  rwa [heq] at hb

/-- A finite family of local providers extends by the zero option to
all candidates. The nodup condition is on original labeled images. -/
theorem finite_injective_provider (f : α → β) (g : α → ℝ) (V : β → ℝ → Prop)
    (xs : List α) (ys : List β) (hn : (xs.map f).Nodup)
    (hm : ∀ x ∈ xs, f x ∈ ys) (hg : ∀ x ∈ xs, 0 ≤ g x)
    (h0 : ∀ y ∈ ys, V y 0) (hv : ∀ x ∈ xs, V (f x) (g x)) :
    ∃ F : β → ℝ, (∀ y, 0 ≤ F y) ∧ (∀ y ∈ ys, V y (F y)) ∧
      (∀ x ∈ xs, F (f x) = g x) ∧ (xs.map g).sum ≤ (ys.map F).sum := by
  classical
  let F : β → ℝ := fun y => if hh : ∃ x ∈ xs, f x = y then g hh.choose else 0
  have hNonneg (y : β) : 0 ≤ F y := by
    dsimp only [F]
    split_ifs with hh
    · exact hg hh.choose hh.choose_spec.1
    · exact le_rfl
  have hValid (y : β) (hy : y ∈ ys) : V y (F y) := by
    dsimp only [F]
    split_ifs with hh
    · have he := hh.choose_spec.2
      exact Eq.mp (congrArg (fun z => V z (g hh.choose)) he) (hv hh.choose hh.choose_spec.1)
    · exact h0 y hy
  have hEq (x : α) (hx : x ∈ xs) : F (f x) = g x := by
    dsimp only [F]
    have hh : ∃ z ∈ xs, f z = f x := ⟨x,hx,rfl⟩
    rw [dif_pos hh]
    have he : hh.choose = x := List.inj_on_of_nodup_map hn hh.choose_spec.1 hx hh.choose_spec.2
    rw [he]
  exact ⟨F,hNonneg,hValid,hEq,list_injective_sum_le f g F xs ys hn hm (fun y _ => hNonneg y) hEq⟩

end
end StrongSilver
