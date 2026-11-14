-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.StrongInterpolation
import StrongSilver.Schedules

namespace StrongSilver
noncomputable section

structure Trace (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (μ : ℝ) (n : ℕ) where
  x : Fin (n+1) → V
  z : Fin (n+1) → V
  g : Fin (n+1) → V
  d : Fin (n+1) → ℝ
  steps : Fin n → ℝ
  split : ∀ i, x i = z i+g i
  nonnegative : ∀ i, 0 ≤ d i
  origin : ∀ i, d i ≤ inner ℝ (g i) (z i)
  supports : ∀ i j, d i+inner ℝ (g i) (z j-z i) ≤ d j
  update : ∀ i : Fin n, x i.succ = x i.castSucc -
    steps i • (μ • x i.castSucc+(1-μ) • g i.castSucc)

theorem iterate_of_updates {V : Type*} [AddCommGroup V] [Module ℝ V]
    (n : ℕ) (steps : Fin n → ℝ) (x : Fin (n+1) → V) (g : V → V)
    (hu : ∀ i : Fin n, x i.succ = x i.castSucc-steps i • g (x i.castSucc)) :
    iterate (List.ofFn steps) g (x 0) = x (Fin.last n) := by
  have hx (t : Fin (n+1)) : iterate ((List.ofFn steps).take t.val) g (x 0) = x t := by
    induction t using Fin.induction with
    | zero => simp [iterate]
    | succ i ih =>
      have hi : i.val < (List.ofFn steps).length := by simpa using i.isLt
      change iterate ((List.ofFn steps).take i.val) g (x 0) = x i.castSucc at ih
      rw [Fin.val_succ,List.take_succ_eq_append_getElem hi,iterate_append,ih]
      simp only [List.getElem_ofFn,iterate,List.foldl_cons,List.foldl_nil]
      exact (hu i).symm
  have hlast := hx (Fin.last n)
  rw [Fin.val_last,List.take_of_length_le (by simp)] at hlast
  exact hlast

theorem Trace.realize {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
    {κ μ : ℝ} {n : ℕ} (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) (T : Trace V μ n) :
    ∃ f : V → ℝ, ∃ G : V → V, Admissible κ f G ∧ f 0 = 0 ∧ (∀ x, 0 ≤ f x) ∧
      (∀ i, G (T.x i) = μ • T.x i+(1-μ) • T.g i) ∧
      (∀ i, f (T.x i) = (μ/2)*‖T.x i‖^2+(1-μ)*(T.d i+‖T.g i‖^2/2)) ∧
      iterate (List.ofFn T.steps) G (T.x 0) = T.x (Fin.last n) := by
  obtain ⟨f,G,hf,hzero,hnonneg,hi⟩ := finite_strong_interpolation hκ hμ hμ1 (n+1) T.z T.g T.d
    T.nonnegative T.origin T.supports
  have hg (i) : G (T.x i) = μ • T.x i+(1-μ) • T.g i := by
    simpa only [T.split] using (hi i).1
  have hv (i) : f (T.x i) = (μ/2)*‖T.x i‖^2+(1-μ)*(T.d i+‖T.g i‖^2/2) := by
    simpa only [T.split] using (hi i).2
  refine ⟨f,G,hf,hzero,hnonneg,hg,hv,?_⟩
  apply iterate_of_updates
  intro i
  rw [hg]
  exact T.update i

/-- A compatible finite trace is realized by an actual objective in the supremum. -/
theorem Trace.distance_lower {κ μ : ℝ} {dimension n : ℕ} (hκ : 1 ≤ κ)
    (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) (T : Trace (Space dimension) μ n) (hx : T.x 0 ≠ 0) :
    ENNReal.ofReal (‖T.x (Fin.last n)‖^2/‖T.x 0‖^2) ≤ D κ (List.ofFn T.steps) := by
  obtain ⟨f,G,hf,hzero,hnonneg,hg,hvalue,hrun⟩ := T.realize hκ hμ hμ1
  let w : Instance κ := {
    dimension := dimension
    f := f
    g := G
    admissible := hf
    start := T.x 0
    minimizer := 0
    minimal := by intro y; rw [hzero]; exact hnonneg y
    distinct := hx
  }
  have hbound := distance_error_le_D (List.ofFn T.steps) w
  simpa only [distanceError,w,hrun,sub_zero] using hbound

end
end StrongSilver
