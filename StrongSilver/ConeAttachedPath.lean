-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeLocalTrajectory
import StrongSilver.PathConcatenation

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1600000
variable {μ b V₀ M H η : ℝ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [ProperSpace (AttachmentSpace V ℂ)]

theorem exists_cone_attached_path {C : ConeConnectorParameters μ b V₀ M H η} {h : List ℝ}
    (L : ConeLocalCertificate C h) {m : ℕ} (Q : SupportedPath V μ m)
    (f : V) (hf : inner ℝ f f = 1) (hY : Q.x 0 = V₀ • f)
    (hV : 0 < V₀) (hη : 0 < η) (hH : 0 ≤ H)
    (hprox : ∀ j, |inner ℝ f (Q.family.z j)| ≤ M*V₀)
    (hslope : ∀ j, |inner ℝ f (Q.family.g j)| ≤ H)
    (hplus : Q.family.Gate (Q.x 0) η) (hminus : Q.family.Gate (Q.x 0) (-η)) :
    ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace V ℂ) μ n,
      J.x 0 = attachmentMap Complex.I f 1 L.x ∧
      J.x (Fin.last n) = retainedMap (W := ℂ) (Q.x (Fin.last m)) ∧
      List.ofFn J.steps = (h++[b])++List.ofFn Q.steps ∧
      ∀ k, (∃ i, J.family.z k = attachmentMap Complex.I f 1 (L.path.family.z i) ∧
        J.family.g k = attachmentMap Complex.I f 1 (L.path.family.g i) ∧ J.family.d k = L.path.family.d i) ∨
        (∃ j, J.family.z k = retainedMap (W := ℂ) (Q.family.z j) ∧
          J.family.g k = retainedMap (W := ℂ) (Q.family.g j) ∧ J.family.d k = Q.family.d j) := by
  let T := attachmentMap Complex.I f 1
  have hT (x y : ℂ) : inner ℝ (T x) (T y) = 1*inner ℝ x y := by
    simpa only [one_pow] using attachment_inner complex_I_inner_self hf 1 x y
  let P := L.path.transport T 1 zero_le_one hT
  let Q₁ := Q.transport (retainedMap (W := ℂ)) 1 zero_le_one (fun x y => by rw [retained_inner,one_mul])
  obtain ⟨hPQ,hQP⟩ := C.attachment_compatible hV hη hH L.path.family Q.family f hf L.supports
    L.proximal_classification hprox hslope (by rwa [← hY]) (by rwa [← hY])
  have hjoin : P.x (Fin.last _) = Q₁.x 0 := by
    change T (L.path.x (Fin.last _)) = retainedMap (W := ℂ) (Q.x 0)
    rw [L.path_end,hY]
    have he : (⟨0,V₀⟩ : ℂ) = V₀ • Complex.I := by
      apply Complex.ext <;> simp
    rw [he]
    simpa only [T,one_mul] using attachment_endpoint complex_I_inner_self f 1 V₀
  let J := P.concatenated Q₁ hPQ hQP
  refine ⟨_,J,rfl,P.concatenated_endpoint Q₁ hPQ hQP hjoin,?_,?_⟩
  · have hh : List.ofFn J.steps = List.ofFn P.steps++List.ofFn Q₁.steps := List.ofFn_get _
    exact hh.trans (congrArg (fun l : List ℝ => l++List.ofFn Q.steps) L.path_steps)
  · intro k
    apply P.concatenated_family_inherits Q₁ hPQ hQP hjoin
      (fun z g d => (∃ i, z = T (L.path.family.z i) ∧ g = T (L.path.family.g i) ∧ d = L.path.family.d i) ∨
        (∃ j, z = retainedMap (W := ℂ) (Q.family.z j) ∧ g = retainedMap (W := ℂ) (Q.family.g j) ∧ d = Q.family.d j))
    · intro i; exact Or.inl ⟨i,rfl,rfl,one_mul _⟩
    · intro j; exact Or.inr ⟨j,rfl,rfl,one_mul _⟩

end
end StrongSilver
