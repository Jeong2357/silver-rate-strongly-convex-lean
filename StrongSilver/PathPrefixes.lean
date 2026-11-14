-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportedPath

namespace StrongSilver.SupportedPath
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {μ : ℝ} {n : ℕ}

theorem follows_prefix (P : SupportedPath V μ n) (G : V → V)
    (hG : ∀ i, G (P.x i.castSucc) = μ • P.x i.castSucc+(1-μ) • P.family.g i)
    (j : Fin (n+1)) : iterate ((List.ofFn P.steps).take j.val) G (P.x 0) = P.x j := by
  induction j using Fin.induction with
  | zero => simp only [Fin.val_zero,List.take_zero,iterate_nil]
  | succ i ih =>
    have hi : i.val < (List.ofFn P.steps).length := by simpa only [List.length_ofFn] using i.isLt
    change iterate ((List.ofFn P.steps).take i.val) G (P.x 0) = P.x i.castSucc at ih
    rw [Fin.val_succ,List.take_succ_eq_append_getElem hi,iterate_append,ih]
    simp only [List.getElem_ofFn,iterate,List.foldl_cons,List.foldl_nil]
    rw [hG]
    exact (P.update i).symm

end
end StrongSilver.SupportedPath
