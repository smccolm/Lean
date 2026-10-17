import Dubon2026.OriginalInternalHomActionContinuity
import Dubon2026.ArithmeticSourceHomContinuity
import Dubon2026.OriginalFiniteRelationModule

/-! # Continuous S-unit dual action for the original finite free cover

The finite stage and finite coefficient make the original free cover a
finitely generated integer lattice. Literal Galois restriction and the
proved arithmetic S-unit action therefore give the dual middle term's
continuity, required by DUB-17's continuous connecting/cup comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(F/K))

/-- Actual arithmetic S-unit-valued Hom on the original finite-stage free cover. -/
abbrev arithmeticRelationFreeSUnitDual :=
  (Rep.ihom (Rep.res
    (AlgEquiv.restrictNormalHom F :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))
    (Rep.free ℤ Gal(F/K) B))).obj (originalArithmeticSUnitRepresentation K Ω a ha)

/-- The actual dual free-cover action is continuous, with the stage
restriction, lattice finiteness and S-unit target action all derived. -/
theorem arithmeticRelationFreeSUnitDualAction_continuous [Finite B]
    [TopologicalSpace (arithmeticRelationFreeSUnitDual K Ω a ha F B)]
    [DiscreteTopology (arithmeticRelationFreeSUnitDual K Ω a ha F B)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
      arithmeticRelationFreeSUnitDual K Ω a ha F B =>
        (arithmeticRelationFreeSUnitDual K Ω a ha F B).ρ z.1 z.2) := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) :=
    AlgEquiv.restrictNormalHom F
  let A := Rep.res π (Rep.free ℤ Gal(F/K) B)
  let C := originalArithmeticSUnitRepresentation K Ω a ha
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : Module.Finite ℤ A := by
    change Module.Finite ℤ (B →₀ Gal(F/K) →₀ ℤ)
    infer_instance
  have hπ : Continuous π := InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField
  have hρ : Continuous (fun z : Gal(F/K) × A => (Rep.free ℤ Gal(F/K) B).ρ z.1 z.2) :=
    continuous_of_discreteTopology
  have hA : Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) × A =>
      A.ρ z.1 z.2) :=
    restrictedCoefficientAction_continuous (Rep.free ℤ Gal(F/K) B) π hπ hρ
  exact originalInternalHomAction_continuous_of_finiteGenerated A C hA
    (originalArithmeticSUnitAction_continuous K Ω a ha)

end
end Dubon2026
