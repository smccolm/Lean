import Dubon2026.LocalFieldNormedUniformizerReciprocity
import Dubon2026.GaloisUnitBaseChangeComposition

/-! # Normed-uniformizer reciprocity on a cyclic subfield

The containing finite Galois field need not be cyclic. The existing normed
uniformizer theorem applies to its cyclic subfield, and literal restriction
composition identifies the resulting Frobenius. This removes the whole
cyclotomic-field cyclicity requirement in the conductor-two route to the
invariant sum formula, full-order class and DUB-17's arithmetic duality.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

section ScalarTowers

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
  (L F : FiniteGaloisIntermediateField K Ω) (M : FiniteGaloisIntermediateField E Ω)
  [IsCyclic Gal(L/K)]
  [Algebra K M] [IsScalarTower K E M]
  [Algebra L F] [IsScalarTower K L F]
  [Algebra F M] [IsScalarTower K F M]
  [Algebra L M] [IsScalarTower K L M] [IsScalarTower L F M]
  [IsScalarTower L M Ω]
  [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]

/-- Actual normed-uniformizer reciprocity on the cyclic subfield is the
restriction of the containing field's arithmetic-Frobenius image. -/
theorem localFieldFiniteCyclicReciprocity_norm_uniformizer_subfield
    (θ : 𝒪[E]) (hθ : Irreducible θ) :
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (Units.map (Algebra.norm K (S := E))
        (Units.mk0 (algebraMap 𝒪[E] E θ) (by intro h; exact hθ.ne_zero (Subtype.ext h)))))).toMul =
      galoisBaseChangeRestriction K K L F
        (galoisBaseChangeRestriction K E F M (localFieldArithmeticFrobenius E M)) := by
  rw [galoisBaseChangeRestriction_comp K K E L F M]
  exact localFieldFiniteCyclicReciprocity_norm_uniformizer K Ω E L M θ hθ

end ScalarTowers

/-- Compatible original embeddings supply all scalar towers for the same
normed-uniformizer formula on the cyclic subfield. -/
theorem localFieldFiniteCyclicReciprocity_norm_uniformizer_embedded_subfield
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (L F : FiniteGaloisIntermediateField K Ω) (M : FiniteGaloisIntermediateField E Ω)
    [IsCyclic Gal(L/K)] [Algebra K M] [IsScalarTower K E M]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
    [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]
    (i : L →ₐ[K] F) (j : F →ₐ[K] M)
    (hi : ∀ x : L, (i x : Ω) = (x : Ω))
    (hj : ∀ x : F, (j x : Ω) = (x : Ω))
    (θ : 𝒪[E]) (hθ : Irreducible θ) :
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (Units.map (Algebra.norm K (S := E))
        (Units.mk0 (algebraMap 𝒪[E] E θ) (by intro h; exact hθ.ne_zero (Subtype.ext h)))))).toMul =
      embeddedNormalGaloisRestriction (F := K) i
        (embeddedNormalGaloisRestriction (F := E) j
          (localFieldArithmeticFrobenius E M)) := by
  letI : Algebra L F := i.toAlgebra
  letI : Algebra F M := j.toAlgebra
  letI : Algebra L M := (j.comp i).toAlgebra
  letI : IsScalarTower K L F := IsScalarTower.of_algHom i
  letI : IsScalarTower K F M := IsScalarTower.of_algHom j
  letI : IsScalarTower K L M := IsScalarTower.of_algHom (j.comp i)
  letI : IsScalarTower L F M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq
    (fun x => ((hj (i x)).trans (hi x)).symm)
  exact localFieldFiniteCyclicReciprocity_norm_uniformizer_subfield K Ω E L F M θ hθ

/-- An actual normed-uniformizer construction supplies the witness for
cyclic-subfield reciprocity; no reciprocity equality is supplied. -/
theorem localFieldFiniteCyclicReciprocity_of_norm_uniformizer_embedded_subfield
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (L F : FiniteGaloisIntermediateField K Ω) (M : FiniteGaloisIntermediateField E Ω)
    [IsCyclic Gal(L/K)] [Algebra K M] [IsScalarTower K E M]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
    (i : L →ₐ[K] F) (j : F →ₐ[K] M)
    (hi : ∀ x : L, (i x : Ω) = (x : Ω))
    (hj : ∀ x : F, (j x : Ω) = (x : Ω)) (x : Kˣ)
    (h : ∃ θ : 𝒪[E], Irreducible θ ∧
      Algebra.norm K (-algebraMap 𝒪[E] E θ) = (x : K) ∧
      Irreducible (algebraMap 𝒪[E] 𝒪[M] θ) ∧ Algebra.FormallyUnramified 𝒪[E] 𝒪[M]) :
    ∃ (_ : Algebra.FormallyUnramified 𝒪[E] 𝒪[M]),
    (localFieldFiniteCyclicReciprocity K Ω L (Additive.ofMul x)).toMul =
        embeddedNormalGaloisRestriction (F := K) i
          (embeddedNormalGaloisRestriction (F := E) j
            (localFieldArithmeticFrobenius E M)) := by
  obtain ⟨θ, hθ, hnorm, _, hunram⟩ := h
  letI := hunram
  have hneg : Irreducible (-θ) := Associated.rfl.neg_left.symm.irreducible hθ
  have hrec := localFieldFiniteCyclicReciprocity_norm_uniformizer_embedded_subfield
    K Ω E L F M i j hi hj (-θ) hneg
  have heq : Units.map (Algebra.norm K (S := E))
      (Units.mk0 (algebraMap 𝒪[E] E (-θ))
        (by intro hz; exact hneg.ne_zero (Subtype.ext hz))) = x := by
    apply Units.ext
    exact hnorm
  rw [heq] at hrec
  exact ⟨hunram, hrec⟩

end
end Dubon2026
