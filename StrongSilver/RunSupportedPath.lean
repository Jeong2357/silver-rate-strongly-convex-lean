-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportedPathProducts
import StrongSilver.Quadratics

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem iterate_prefix_succ (h : List ℝ) (G : V → V) (x : V) (i : Fin h.length) :
    iterate (h.take (i.val+1)) G x = iterate (h.take i.val) G x-
      h.get i • G (iterate (h.take i.val) G x) := by
  rw [List.take_succ_eq_append_getElem i.isLt,iterate_append]
  rfl

namespace SupportedPath
variable [ProperSpace V]

def ofRun (P : Moreau.Epigraph V) (μ : ℝ) (h : List ℝ) (a : V) : SupportedPath V μ h.length :=
  ofMoreau P (fun i => h.get i) (fun i => iterate (h.take i.val) (stronglyConvexGradient μ (Moreau.gradient P)) a)
    (fun i => iterate_prefix_succ h _ a i)

theorem ofRun_start (P : Moreau.Epigraph V) (μ : ℝ) (h : List ℝ) (a : V) :
    (ofRun P μ h a).x 0 = a := rfl

theorem ofRun_end (P : Moreau.Epigraph V) (μ : ℝ) (h : List ℝ) (a : V) :
    (ofRun P μ h a).x (Fin.last h.length) = iterate h (stronglyConvexGradient μ (Moreau.gradient P)) a := by
  change iterate (h.take h.length) _ a = _
  rw [List.take_length]

def quadraticRun (μ : ℝ) (h : List ℝ) (a : V) : SupportedPath V μ h.length :=
  quadratic (fun i => h.get i) (fun i => iterate (h.take i.val) (fun x => μ • x) a) (by
    intro i
    simp only [Fin.val_succ,Fin.val_castSucc]
    rw [iterate_prefix_succ h (fun x => μ • x) a i]
    module)

theorem quadraticRun_start (μ : ℝ) (h : List ℝ) (a : V) : (quadraticRun μ h a).x 0 = a := rfl

theorem quadraticRun_end (μ : ℝ) (h : List ℝ) (a : V) :
    (quadraticRun μ h a).x (Fin.last h.length) = quadraticMultiplier μ h • a := by
  change iterate (h.take h.length) (fun x => μ • x) a = _
  rw [List.take_length,quadratic_iterate]

end SupportedPath
end
end StrongSilver
