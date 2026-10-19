import Dubon2026.ContinuousGaloisFiniteFactors
import Dubon2026.EmbeddedNormalGaloisRestriction

/-! Enlarge the actual finite factor of a continuous deformation to contain
its actual cyclotomic field. The finite compositum and normal restriction
preserve the same global representation. This removes the root-containment
input from cyclotomic inertia descent in the local-ring chain for Theorem 2.6. -/

namespace Dubon2026
noncomputable section

/-- A continuous discrete Galois representation has an actual finite
Galois factor containing any prescribed finite Galois intermediate field. -/
theorem continuous_galois_finite_factor_containing
    {K Ω T : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (χ : Gal(Ω/K) →ₜ* T) (C : FiniteGaloisIntermediateField K Ω) :
    ∃ F : FiniteGaloisIntermediateField K Ω, C ≤ F ∧
      ∃ ψ : Gal(F/K) →* T, ∀ g : Gal(Ω/K),
        ψ (AlgEquiv.restrictNormalHom F g) = χ g := by
  obtain ⟨F₀, ψ₀, hψ₀⟩ := continuous_galois_finite_factor χ
  let F := F₀ ⊔ C
  let i : F₀ →ₐ[K] F := IntermediateField.inclusion (show F₀.toIntermediateField ≤ F.toIntermediateField from le_sup_left)
  let r := embeddedNormalGaloisRestriction (F := K) i
  refine ⟨F, le_sup_right, ψ₀.comp r, ?_⟩
  intro g
  have he : r (AlgEquiv.restrictNormalHom F g) = AlgEquiv.restrictNormalHom F₀ g := by
    apply AlgEquiv.ext
    intro x
    apply F₀.toIntermediateField.val.injective
    have hr := embeddedNormalGaloisRestriction_commutes (F := K) i (AlgEquiv.restrictNormalHom F g) x
    have hr' := congrArg (fun y : F => (y : Ω)) hr
    exact hr'.trans ((g.restrictNormal_commutes F (i x)).trans
      (g.restrictNormal_commutes F₀ x).symm)
  change ψ₀ (r (AlgEquiv.restrictNormalHom F g)) = χ g
  rw [he]
  exact hψ₀ g

end
end Dubon2026
