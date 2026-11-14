-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.RunSupportedPath
import StrongSilver.ExactProximalValues
import StrongSilver.PhaseCoordinates

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000
variable {A μ : ℝ}

def localPhasePath (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a : ℝ) : SupportedPath PhaseSpace μ (h++[b]).length :=
  (SupportedPath.ofRun C.body.supportEpigraph μ (h++[b]) R).prod
    ((SupportedPath.quadraticRun μ (h++[b]) D).prod
      (SupportedPath.ofRun S.epigraph μ (h++[b]) a) rfl) rfl

theorem localPhasePath_start (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a : ℝ) :
    (localPhasePath C S h b R D a).x 0 = phasePoint R D a := rfl

theorem localPhasePath_end (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a e : ℝ)
    (hR : iterate h C.physical R = (⟨planarEpsilon A,1⟩ : ℂ))
    (ha : iterate h (S.physical μ) a = e) (hselected : e-b*S.physical μ e = 0) :
    (localPhasePath C S h b R D a).x (Fin.last (h++[b]).length) =
      phasePoint (-(b-1) • (⟨planarEpsilon A,1⟩ : ℂ))
        ((quadraticMultiplier μ h*(1-μ*b))*D) 0 := by
  change phasePoint ((SupportedPath.ofRun C.body.supportEpigraph μ (h++[b]) R).x _)
    ((SupportedPath.quadraticRun μ (h++[b]) D).x _)
    ((SupportedPath.ofRun S.epigraph μ (h++[b]) a).x _) = _
  rw [SupportedPath.ofRun_end,SupportedPath.quadraticRun_end,SupportedPath.ofRun_end]
  change phasePoint (iterate (h++[b]) C.physical R) (quadraticMultiplier μ (h++[b])*D)
    (iterate (h++[b]) (S.physical μ) a) = _
  rw [iterate_append,iterate_append,hR,ha]
  have hC := selected_step_at_body_point C.body_terminal_mem μ b
  change (⟨planarEpsilon A,1⟩ : ℂ)-b • C.physical (⟨planarEpsilon A,1⟩ : ℂ) =
    -(b-1) • (⟨planarEpsilon A,1⟩ : ℂ) at hC
  have hmult : quadraticMultiplier μ (h++[b]) = quadraticMultiplier μ h*(1-μ*b) := by
    simp only [quadraticMultiplier,List.map_append,List.prod_append,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one]
  simp only [iterate,List.foldl_cons,List.foldl_nil,smul_eq_mul]
  rw [hC,hselected,hmult]

theorem localPhasePath_slope (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a : ℝ) (i : Fin (h++[b]).length) :
    (localPhasePath C S h b R D a).family.g i =
      phaseSlope (C.body.projection (iterate ((h++[b]).take i.val) C.physical R))
        (S.g (iterate ((h++[b]).take i.val) (S.physical μ) a)) := by
  change phasePoint (Moreau.gradient C.body.supportEpigraph (iterate ((h++[b]).take i.val) C.physical R)) 0
    (Moreau.gradient S.epigraph (iterate ((h++[b]).take i.val) (S.physical μ) a)) = _
  rw [C.body.support_envelope_gradient,S.envelope_gradient]
  rfl

theorem localPhasePath_proximal (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a : ℝ) (i : Fin (h++[b]).length) :
    let Ri := iterate ((h++[b]).take i.val) C.physical R
    let ai := iterate ((h++[b]).take i.val) (S.physical μ) a
    (localPhasePath C S h b R D a).family.z i =
      phasePoint (Ri-C.body.projection Ri) (quadraticMultiplier μ ((h++[b]).take i.val)*D) (S.proximalMap ai) := by
  dsimp only
  change phasePoint (Moreau.proximal C.body.supportEpigraph (iterate ((h++[b]).take i.val) C.physical R))
    (iterate ((h++[b]).take i.val) (fun t => μ • t) D)
    (Moreau.proximal S.epigraph (iterate ((h++[b]).take i.val) (S.physical μ) a)) = _
  rw [Moreau.proximal,C.body.exact_proximal_values,Moreau.proximal,S.exact_proximal_values,quadratic_iterate]
  rfl

theorem localPhasePath_height (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a : ℝ) (i : Fin (h++[b]).length) :
    let Ri := iterate ((h++[b]).take i.val) C.physical R
    let ai := iterate ((h++[b]).take i.val) (S.physical μ) a
    (localPhasePath C S h b R D a).family.d i = C.body.supportValue (Ri-C.body.projection Ri)+
      S.potential (S.proximalMap ai) := by
  dsimp only
  change (Moreau.minimizingPair C.body.supportEpigraph (iterate ((h++[b]).take i.val) C.physical R)).2+
    (0+(Moreau.minimizingPair S.epigraph (iterate ((h++[b]).take i.val) (S.physical μ) a)).2) = _
  rw [C.body.exact_proximal_values,S.exact_proximal_values]
  simp only [zero_add]

end
end StrongSilver
