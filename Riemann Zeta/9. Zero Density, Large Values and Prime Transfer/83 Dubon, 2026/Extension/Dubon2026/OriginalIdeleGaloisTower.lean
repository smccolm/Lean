import Dubon2026.OriginalIdeleBaseChangeTower
import Dubon2026.OriginalDecompositionAlgebraTower

/-! # Original Galois actions commute with tower embeddings

Normal restriction acts on the literal original primes and completed
fields. Density extends the field identity to completion maps, hence to
the actual ideles and classes. These are the equivariance identities
needed to partition the original Galois norm in a tower and to prove
coprime cyclotomic descent for DUB-17's cyclic norm-index dependency.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain UniformSpace
open scoped NumberField
variable (K E L : Type) [Field K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [IsGalois K E]

/-- Original local transport commutes with normal restriction and actual
completion base change. -/
theorem originalAdicBaseChangeMap_restrictNormal
    (u u' : HeightOneSpectrum (𝓞 E)) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver u.asIdeal] [w'.asIdeal.LiesOver u'.asIdeal]
    (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ w = w')
    (hτ : numberFieldGaloisPlaceEquiv K E (AlgEquiv.restrictNormalHom E σ) u = u')
    (x : u.adicCompletion E) :
    numberFieldGaloisLocalTransport K L σ w w' hσ (originalAdicBaseChangeMap E L u w x) =
      originalAdicBaseChangeMap E L u' w'
        (numberFieldGaloisLocalTransport K E (AlgEquiv.restrictNormalHom E σ) u u' hτ x) := by
  induction x using Completion.induction_on
  · exact isClosed_eq
      ((numberFieldGaloisLocalTransport_continuous K L σ w w' hσ).comp
        (originalAdicBaseChangeMap_continuous E L u w))
      ((originalAdicBaseChangeMap_continuous E L u' w').comp
        (numberFieldGaloisLocalTransport_continuous K E (AlgEquiv.restrictNormalHom E σ) u u' hτ))
  · rename_i x
    change numberFieldGaloisLocalTransport K L σ w w' hσ
      (originalAdicBaseChangeMap E L u w (algebraMap E (u.adicCompletion E) x.ofVal)) =
        originalAdicBaseChangeMap E L u' w'
          (numberFieldGaloisLocalTransport K E (AlgEquiv.restrictNormalHom E σ) u u' hτ
            (algebraMap E (u.adicCompletion E) x.ofVal))
    rw [originalAdicBaseChangeMap_algebraMap, numberFieldGaloisLocalTransport_algebraMap,
      numberFieldGaloisLocalTransport_algebraMap, originalAdicBaseChangeMap_algebraMap]
    exact congrArg (algebraMap L (w'.adicCompletion L)) (AlgEquiv.restrictNormal_commutes σ E x.ofVal).symm

/-- Actual finite-adele base change intertwines the original normal restriction. -/
theorem originalFiniteAdeleBaseChangeMap_restrictNormal
    (σ : Gal(L/K)) (a : FiniteAdeleRing (𝓞 E) E) :
    numberFieldFiniteAdeleGaloisMap K L σ (originalFiniteAdeleBaseChangeMap E L a) =
      originalFiniteAdeleBaseChangeMap E L
        (numberFieldFiniteAdeleGaloisMap K E (AlgEquiv.restrictNormalHom E σ) a) := by
  apply FiniteAdeleRing.ext
  intro w'
  let w := (numberFieldGaloisPlaceEquiv K L σ).symm w'
  let u := originalFinitePrimeBelow E L w
  let u' := originalFinitePrimeBelow E L w'
  have hσ : numberFieldGaloisPlaceEquiv K L σ w = w' :=
    (numberFieldGaloisPlaceEquiv K L σ).apply_symm_apply w'
  have hτ : numberFieldGaloisPlaceEquiv K E (AlgEquiv.restrictNormalHom E σ) u = u' := by
    rw [← originalFinitePrimeBelow_restrictNormal_algebraTower K E L, hσ]
  letI : w.asIdeal.LiesOver u.asIdeal := originalFinitePrimeBelow_liesOver E L w
  letI : w'.asIdeal.LiesOver u'.asIdeal := originalFinitePrimeBelow_liesOver E L w'
  rw [numberFieldFiniteAdeleGaloisMap_apply K L σ _ w w' hσ,
    originalFiniteAdeleBaseChangeMap_apply_at E L a u w rfl,
    originalFiniteAdeleBaseChangeMap_apply_at E L _ u' w' rfl,
    numberFieldFiniteAdeleGaloisMap_apply K E (AlgEquiv.restrictNormalHom E σ) a u u' hτ]
  exact originalAdicBaseChangeMap_restrictNormal K E L u u' w w' σ hσ hτ (a u)

/-- Actual infinite-adele base change intertwines the original normal restriction. -/
theorem originalInfiniteAdeleBaseChangeMap_restrictNormal
    (σ : Gal(L/K)) (a : InfiniteAdeleRing E) :
    numberFieldInfiniteAdeleGaloisMap K L σ (originalInfiniteAdeleBaseChangeMap E L a) =
      originalInfiniteAdeleBaseChangeMap E L
        (numberFieldInfiniteAdeleGaloisMap K E (AlgEquiv.restrictNormalHom E σ) a) := by
  letI : T2Space (InfiniteAdeleRing L) :=
    inferInstanceAs (T2Space ((w : InfinitePlace L) → w.Completion))
  refine (InfiniteAdeleRing.denseRange_algebraMap E).induction_on a ?_ ?_
  · exact isClosed_eq
      ((numberFieldInfiniteAdeleGaloisMap_continuous K L σ).comp
        (originalInfiniteAdeleBaseChangeMap_isClosedEmbedding E L).continuous)
      ((originalInfiniteAdeleBaseChangeMap_isClosedEmbedding E L).continuous.comp
        (numberFieldInfiniteAdeleGaloisMap_continuous K E (AlgEquiv.restrictNormalHom E σ)))
  · intro x
    rw [originalInfiniteAdeleBaseChangeMap_algebraMap, numberFieldInfiniteAdeleGaloisMap_algebraMap,
      numberFieldInfiniteAdeleGaloisMap_algebraMap, originalInfiniteAdeleBaseChangeMap_algebraMap]
    exact congrArg (algebraMap L (InfiniteAdeleRing L)) (AlgEquiv.restrictNormal_commutes σ E x).symm

/-- The actual original idele embedding is equivariant under normal restriction. -/
theorem originalIdeleBaseChangeMap_restrictNormal
    (σ : Gal(L/K)) (a : (AdeleRing (𝓞 E) E)ˣ) :
    numberFieldIdeleGaloisMap K L σ (originalIdeleBaseChangeMap E L a) =
      originalIdeleBaseChangeMap E L
        (numberFieldIdeleGaloisMap K E (AlgEquiv.restrictNormalHom E σ) a) := by
  apply Units.ext
  exact Prod.ext (originalInfiniteAdeleBaseChangeMap_restrictNormal K E L σ a.val.1)
    (originalFiniteAdeleBaseChangeMap_restrictNormal K E L σ a.val.2)

/-- The actual original class embedding is equivariant under normal restriction. -/
theorem originalIdeleClassBaseChangeMap_restrictNormal
    (σ : Gal(L/K)) (a : OriginalNumberFieldIdeleClassGroup E) :
    numberFieldIdeleClassGaloisMap K L σ (originalIdeleClassBaseChangeMap E L a) =
      originalIdeleClassBaseChangeMap E L
        (numberFieldIdeleClassGaloisMap K E (AlgEquiv.restrictNormalHom E σ) a) := by
  induction a using QuotientGroup.induction_on
  rename_i a
  change numberFieldIdeleClassGaloisMap K L σ
    (originalIdeleClassBaseChangeMap E L (QuotientGroup.mk' (numberFieldPrincipalIdele E).range a)) =
      originalIdeleClassBaseChangeMap E L
        (numberFieldIdeleClassGaloisMap K E (AlgEquiv.restrictNormalHom E σ)
          (QuotientGroup.mk' (numberFieldPrincipalIdele E).range a))
  rw [originalIdeleClassBaseChangeMap_mk, numberFieldIdeleClassGaloisMap_mk,
    numberFieldIdeleClassGaloisMap_mk, originalIdeleClassBaseChangeMap_mk,
    originalIdeleBaseChangeMap_restrictNormal]

end
end Dubon2026
