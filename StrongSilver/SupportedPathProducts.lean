-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportedPath
import StrongSilver.SupportProducts
import StrongSilver.EpigraphSupportFamily

namespace StrongSilver.SupportedPath
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {μ : ℝ} {n : ℕ}

def prod (P : SupportedPath V μ n) (Q : SupportedPath W μ n) (hsteps : P.steps = Q.steps) :
    SupportedPath (WithLp 2 (V × W)) μ n where
  x := fun i => WithLp.toLp 2 (P.x i,Q.x i)
  family := P.family.prod Q.family
  steps := P.steps
  split := by
    intro i
    apply WithLp.ofLp_injective 2
    change (P.x i.castSucc,Q.x i.castSucc) = (P.family.z i+P.family.g i,Q.family.z i+Q.family.g i)
    rw [P.split,Q.split]
  update := by
    intro i
    apply WithLp.ofLp_injective 2
    change (P.x i.succ,Q.x i.succ) =
      (P.x i.castSucc-P.steps i • (μ • P.x i.castSucc+(1-μ) • P.family.g i),
       Q.x i.castSucc-P.steps i • (μ • Q.x i.castSucc+(1-μ) • Q.family.g i))
    rw [P.update,Q.update,hsteps]

def quadratic (steps : Fin n → ℝ) (x : Fin (n+1) → V)
    (hu : ∀ i : Fin n, x i.succ = (1-μ*steps i) • x i.castSucc) : SupportedPath V μ n where
  x := x
  family := SupportFamily.zeroSlopes (fun i => x i.castSucc)
  steps := steps
  split := by intro i; exact (add_zero _).symm
  update := by
    intro i
    rw [hu]
    change (1-μ*steps i) • x i.castSucc = x i.castSucc-steps i • (μ • x i.castSucc+(1-μ) • (0 : V))
    module

variable [ProperSpace V]

def ofMoreau (P : Moreau.Epigraph V) (steps : Fin n → ℝ) (x : Fin (n+1) → V)
    (hu : ∀ i : Fin n, x i.succ = x i.castSucc-
      steps i • stronglyConvexGradient μ (Moreau.gradient P) (x i.castSucc)) : SupportedPath V μ n where
  x := x
  family := SupportFamily.ofEpigraph P (fun i => x i.castSucc)
  steps := steps
  split := fun i => SupportFamily.ofEpigraph_split P (fun i => x i.castSucc) i
  update := hu

end
end StrongSilver.SupportedPath
