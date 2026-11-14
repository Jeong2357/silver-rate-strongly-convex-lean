-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Schedules

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem exists_backward_path_in_set (h : List ℝ) (G : V → V) (S : Set V)
    (hstep : ∀ b ∈ h, ∀ y ∈ S, ∃ x ∈ S, x-b • G x = y) {y : V} (hy : y ∈ S) :
    ∃ x ∈ S, iterate h G x = y ∧ ∀ i : ℕ, i ≤ h.length → iterate (h.take i) G x ∈ S := by
  induction h generalizing y with
  | nil => exact ⟨y,hy,rfl,fun i hi => by simpa only [List.take_nil,iterate_nil] using hy⟩
  | cons b h ih =>
    obtain ⟨z,hz,hzy,hstates⟩ := ih (fun c hc => hstep c (List.mem_cons_of_mem b hc)) hy
    obtain ⟨x,hx,hxz⟩ := hstep b List.mem_cons_self z hz
    refine ⟨x,hx,by rw [iterate_cons,hxz,hzy],fun i hi => ?_⟩
    cases i with
    | zero => simpa only [List.take_zero,iterate_nil] using hx
    | succ i =>
      rw [List.take_succ_cons,iterate_cons,hxz]
      exact hstates i (by simp only [List.length_cons] at hi; omega)

theorem iterate_prefix_ne_zero {h : List ℝ} {G : V → V} {x y : V} (hG0 : G 0 = 0)
    (hend : iterate h G x = y) (hy : y ≠ 0) (i : ℕ) : iterate (h.take i) G x ≠ 0 := by
  intro he
  have hh : iterate (h.drop i) G (iterate (h.take i) G x) = y := by
    rw [← iterate_append,List.take_append_drop,hend]
  rw [he,iterate_fixed (h.drop i) G 0 hG0] at hh
  exact hy hh.symm

end
end StrongSilver
