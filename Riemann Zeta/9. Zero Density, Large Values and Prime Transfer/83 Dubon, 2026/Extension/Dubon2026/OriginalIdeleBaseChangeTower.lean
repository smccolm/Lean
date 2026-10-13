import Dubon2026.OriginalIdeleClassBaseChange
import Dubon2026.OriginalPrimeTowerSelection

/-! # Composition of the original idele and class embeddings

The original finite completion maps compose by density, and contraction
of the original primes gives composition on the restricted product. At
infinity, the pinned density of the original number field gives the same
identity directly. Thus the actual original idele and class embeddings
compose in an algebra tower. These identities are required for norm
transitivity and coprime cyclotomic descent, removing the primitive-root
assumption from DUB-17's original norm-index dependency. No substitute
adele ring or assumed norm-compatibility certificate is introduced.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain UniformSpace
open scoped NumberField
variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]

/-- The actual finite-completion embeddings compose in the original tower. -/
theorem originalAdicBaseChangeMap_tower
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]
    [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    originalAdicBaseChangeMap E L u w (originalAdicBaseChangeMap K E v u x) =
      originalAdicBaseChangeMap K L v w x := by
  induction x using Completion.induction_on
  · exact isClosed_eq
      ((originalAdicBaseChangeMap_continuous E L u w).comp
        (originalAdicBaseChangeMap_continuous K E v u))
      (originalAdicBaseChangeMap_continuous K L v w)
  · rename_i x
    change originalAdicBaseChangeMap E L u w
      (originalAdicBaseChangeMap K E v u (algebraMap K (v.adicCompletion K) x.ofVal)) =
        originalAdicBaseChangeMap K L v w (algebraMap K (v.adicCompletion K) x.ofVal)
    rw [originalAdicBaseChangeMap_algebraMap, originalAdicBaseChangeMap_algebraMap,
      originalAdicBaseChangeMap_algebraMap, IsScalarTower.algebraMap_apply K E L]

/-- Composition holds on the actual original finite restricted products. -/
theorem originalFiniteAdeleBaseChangeMap_tower (a : FiniteAdeleRing (𝓞 K) K) :
    originalFiniteAdeleBaseChangeMap E L (originalFiniteAdeleBaseChangeMap K E a) =
      originalFiniteAdeleBaseChangeMap K L a := by
  apply FiniteAdeleRing.ext
  intro w
  let u := originalFinitePrimeBelow E L w
  let v := originalFinitePrimeBelow K L w
  have hu : originalFinitePrimeBelow K E u = v := originalFinitePrimeBelow_tower K E L w
  letI : w.asIdeal.LiesOver u.asIdeal := originalFinitePrimeBelow_liesOver E L w
  letI : w.asIdeal.LiesOver v.asIdeal := originalFinitePrimeBelow_liesOver K L w
  letI : u.asIdeal.LiesOver v.asIdeal := by
    rw [← hu]
    exact originalFinitePrimeBelow_liesOver K E u
  rw [originalFiniteAdeleBaseChangeMap_apply_at E L _ u w rfl,
    originalFiniteAdeleBaseChangeMap_apply_at K E a v u hu,
    originalFiniteAdeleBaseChangeMap_apply_at K L a v w rfl]
  exact originalAdicBaseChangeMap_tower K E L v u w (a v)

/-- Pinned field density proves composition on the original infinite adeles. -/
theorem originalInfiniteAdeleBaseChangeMap_tower (a : InfiniteAdeleRing K) :
    originalInfiniteAdeleBaseChangeMap E L (originalInfiniteAdeleBaseChangeMap K E a) =
      originalInfiniteAdeleBaseChangeMap K L a := by
  letI : T2Space (InfiniteAdeleRing L) :=
    inferInstanceAs (T2Space ((w : InfinitePlace L) → w.Completion))
  refine (InfiniteAdeleRing.denseRange_algebraMap K).induction_on a ?_ ?_
  · exact isClosed_eq
      ((originalInfiniteAdeleBaseChangeMap_isClosedEmbedding E L).continuous.comp
        (originalInfiniteAdeleBaseChangeMap_isClosedEmbedding K E).continuous)
      (originalInfiniteAdeleBaseChangeMap_isClosedEmbedding K L).continuous
  · intro x
    rw [originalInfiniteAdeleBaseChangeMap_algebraMap,
      originalInfiniteAdeleBaseChangeMap_algebraMap,
      originalInfiniteAdeleBaseChangeMap_algebraMap, IsScalarTower.algebraMap_apply K E L]

/-- Composition on the actual full original adele rings. -/
theorem originalAdeleBaseChangeMap_tower (a : AdeleRing (𝓞 K) K) :
    originalAdeleBaseChangeMap E L (originalAdeleBaseChangeMap K E a) =
      originalAdeleBaseChangeMap K L a :=
  Prod.ext (originalInfiniteAdeleBaseChangeMap_tower K E L a.1)
    (originalFiniteAdeleBaseChangeMap_tower K E L a.2)

/-- Composition on the units of the actual original adele rings. -/
theorem originalIdeleBaseChangeMap_tower (a : (AdeleRing (𝓞 K) K)ˣ) :
    originalIdeleBaseChangeMap E L (originalIdeleBaseChangeMap K E a) =
      originalIdeleBaseChangeMap K L a :=
  Units.ext (originalAdeleBaseChangeMap_tower K E L a.val)

/-- Composition on the actual original idele-class groups. -/
theorem originalIdeleClassBaseChangeMap_tower (a : OriginalNumberFieldIdeleClassGroup K) :
    originalIdeleClassBaseChangeMap E L (originalIdeleClassBaseChangeMap K E a) =
      originalIdeleClassBaseChangeMap K L a := by
  induction a using QuotientGroup.induction_on
  rename_i a
  change originalIdeleClassBaseChangeMap E L
    (originalIdeleClassBaseChangeMap K E (QuotientGroup.mk' (numberFieldPrincipalIdele K).range a)) =
      originalIdeleClassBaseChangeMap K L (QuotientGroup.mk' (numberFieldPrincipalIdele K).range a)
  rw [originalIdeleClassBaseChangeMap_mk, originalIdeleClassBaseChangeMap_mk,
    originalIdeleClassBaseChangeMap_mk, originalIdeleBaseChangeMap_tower]

end
end Dubon2026
