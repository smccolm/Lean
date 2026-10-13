import Dubon2026.OriginalFiniteAdeleFixedDescent
import Dubon2026.OriginalInfiniteAdeleFixedDescent
import Dubon2026.NumberFieldIdeleGaloisAction

/-! # Actual full-adele base change and fixed-point descent

The already proved finite restricted-product and infinite-product
comparisons are assembled on the actual original adele rings. This is
the ring-level descent required for the original idele/class norm quotient
on DUB-17's arithmetic duality, Selmer and automorphy dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The actual base-change map on the original full adele rings. -/
def originalAdeleBaseChangeMap : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (originalInfiniteAdeleBaseChangeMap K L) (originalFiniteAdeleBaseChangeMap K L)

/-- Original full-adele base change is injective. -/
theorem originalAdeleBaseChangeMap_injective : Function.Injective (originalAdeleBaseChangeMap K L) := by
  intro a b hab
  exact Prod.ext
    ((originalInfiniteAdeleBaseChangeMap_isClosedEmbedding K L).injective (congrArg Prod.fst hab))
    ((originalFiniteAdeleBaseChangeMap_injective K L) (congrArg Prod.snd hab))

/-- The original full-adele map extends the actual original global-field embedding. -/
theorem originalAdeleBaseChangeMap_algebraMap (x : K) :
    originalAdeleBaseChangeMap K L (algebraMap K (AdeleRing (𝓞 K) K) x) =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x) :=
  Prod.ext (originalInfiniteAdeleBaseChangeMap_algebraMap K L x)
    (originalFiniteAdeleBaseChangeMap_algebraMap K L x)

/-- Every original base adele is fixed by the actual original Galois action. -/
theorem originalAdeleBaseChangeMap_fixed (σ : Gal(L/K)) (a : AdeleRing (𝓞 K) K) :
    numberFieldAdeleGaloisMap K L σ (originalAdeleBaseChangeMap K L a) =
      originalAdeleBaseChangeMap K L a :=
  Prod.ext (originalInfiniteAdeleBaseChangeMap_fixed K L σ a.1)
    (originalFiniteAdeleBaseChangeMap_fixed K L σ a.2)

/-- Every fixed original full adele is the image of an actual original base adele. -/
theorem originalAdeleBaseChangeMap_surjective_fixed [FiniteDimensional K L] [IsGalois K L]
    (a : AdeleRing (𝓞 L) L) (ha : ∀ σ : Gal(L/K), numberFieldAdeleGaloisMap K L σ a = a) :
    ∃ b : AdeleRing (𝓞 K) K, originalAdeleBaseChangeMap K L b = a := by
  obtain ⟨bInf, hbInf⟩ := originalInfiniteAdeleBaseChangeMap_surjective_fixed K L a.1
    (fun σ => congrArg Prod.fst (ha σ))
  obtain ⟨bf, hbf⟩ := originalFiniteAdeleBaseChangeMap_surjective_fixed K L a.2
    (fun σ => congrArg Prod.snd (ha σ))
  exact ⟨(bInf, bf), Prod.ext hbInf hbf⟩

end
end Dubon2026
