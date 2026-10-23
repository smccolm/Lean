import Dubon2026.SourceCoefficientIntegralMinimalPolynomial

/-! Actual modular-field embeddings with prescribed transcendental j are
identified with roots of the same constructed integral modular polynomial,
and the correspondence sends an embedding to its original j_N value.
The elliptic cyclic-subgroup interpretation of these roots and the inertia
orbit map remain required for the DUB-17/18 finite exceptional-fiber census. -/
namespace Dubon2026.SourceFunctionField.CoefficientPresentation
noncomputable section
open IntermediateField Polynomial
open scoped IntermediateField
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] {j₀ : Ω}

theorem specialized_minpoly_eq_modularPolynomial (hNK : (N : K) ≠ 0)
    (hj₀ : Transcendental K j₀) :
    (minpoly K⟮jCoeff N K⟯ (jN N K)).map (coordinateSpecialization N K hj₀).toRingHom =
      relationAtSeed (IntegralJCoordinate.modularPolynomial N) j₀ := by
  rw [minpoly_level_eq_modularPolynomial N K hNK, relationAtSeed,
    Polynomial.map_map, relationAtSeed]
  congr 1
  apply Polynomial.ringHom_ext' (RingHom.ext_int _ _)
  simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X]
  exact coordinateSpecialization_gen N K hj₀

/-- The exact actual embeddings-to-integral-modular-roots correspondence. -/
def embeddingsEquivModularRoots (hNK : (N : K) ≠ 0) (hj₀ : Transcendental K j₀) :
    {ψ : modularFunctionFieldCoeff N K →ₐ[K] Ω // ψ (jCoeff N K) = j₀} ≃
      {y : Ω // (relationAtSeed (IntegralJCoordinate.modularPolynomial N) j₀).IsRoot y} :=
  (embeddingsEquivRoots N K hNK hj₀).trans (Equiv.subtypeEquivRight fun y => by
    rw [specialized_minpoly_eq_modularPolynomial N K hNK hj₀])

theorem embeddingsEquivModularRoots_apply (hNK : (N : K) ≠ 0) (hj₀ : Transcendental K j₀)
    (ψ : {ψ : modularFunctionFieldCoeff N K →ₐ[K] Ω // ψ (jCoeff N K) = j₀}) :
    (embeddingsEquivModularRoots N K hNK hj₀ ψ).1 = ψ.1 (jN N K) :=
  embeddingsEquivRoots_apply N K hNK hj₀ ψ

end
end Dubon2026.SourceFunctionField.CoefficientPresentation
