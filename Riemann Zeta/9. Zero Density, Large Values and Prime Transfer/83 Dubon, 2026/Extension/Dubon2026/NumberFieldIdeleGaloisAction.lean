import Dubon2026.NumberFieldFiniteAdeleGaloisAction
import Dubon2026.NumberFieldInfiniteAdeleGaloisAction
import Dubon2026.NumberFieldIdeleSupport

/-! # The actual Galois action on the original full ideles

Both original adelic factors carry their proved actions. Passing to
their actual units gives the full idele action and proves equivariance
of the original principal image for DUB-17's supported exact sequence.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The original Galois ring map on the full original adele ring. -/
def numberFieldAdeleGaloisMap (σ : Gal(L/K)) : AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (numberFieldInfiniteAdeleGaloisMap K L σ) (numberFieldFiniteAdeleGaloisMap K L σ)

/-- The original full adelic map agrees with the original diagonal action. -/
theorem numberFieldAdeleGaloisMap_algebraMap (σ : Gal(L/K)) (x : L) :
    numberFieldAdeleGaloisMap K L σ (algebraMap L (AdeleRing (𝓞 L) L) x) =
      algebraMap L (AdeleRing (𝓞 L) L) (σ x) :=
  Prod.ext (numberFieldInfiniteAdeleGaloisMap_algebraMap K L σ x)
    (numberFieldFiniteAdeleGaloisMap_algebraMap K L σ x)

/-- The actual Galois map on the units of the original adele ring. -/
def numberFieldIdeleGaloisMap (σ : Gal(L/K)) :
    (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (numberFieldAdeleGaloisMap K L σ).toMonoidHom

/-- Identity acts identically on the original full ideles. -/
theorem numberFieldIdeleGaloisMap_one (a : (AdeleRing (𝓞 L) L)ˣ) :
    numberFieldIdeleGaloisMap K L 1 a = a := by
  apply Units.ext
  exact Prod.ext (numberFieldInfiniteAdeleGaloisMap_one K L a.val.1)
    (numberFieldFiniteAdeleGaloisMap_one K L a.val.2)

/-- Products of original automorphisms compose their actual full-idele maps. -/
theorem numberFieldIdeleGaloisMap_mul (σ τ : Gal(L/K)) (a : (AdeleRing (𝓞 L) L)ˣ) :
    numberFieldIdeleGaloisMap K L (σ * τ) a =
      numberFieldIdeleGaloisMap K L σ (numberFieldIdeleGaloisMap K L τ a) := by
  apply Units.ext
  exact Prod.ext (numberFieldInfiniteAdeleGaloisMap_mul K L σ τ a.val.1)
    (numberFieldFiniteAdeleGaloisMap_mul K L σ τ a.val.2)

/-- The actual original Galois action on the original full ideles. -/
@[reducible]
def numberFieldIdeleGaloisAction : MulDistribMulAction Gal(L/K) (AdeleRing (𝓞 L) L)ˣ where
  smul σ a := numberFieldIdeleGaloisMap K L σ a
  one_smul := numberFieldIdeleGaloisMap_one K L
  mul_smul := numberFieldIdeleGaloisMap_mul K L
  smul_one σ := map_one (numberFieldIdeleGaloisMap K L σ)
  smul_mul σ := map_mul (numberFieldIdeleGaloisMap K L σ)

/-- The original principal-idele embedding intertwines the two actual Galois actions. -/
theorem numberFieldPrincipalIdele_galois (σ : Gal(L/K)) (x : Lˣ) :
    numberFieldIdeleGaloisMap K L σ (numberFieldPrincipalIdele L x) =
      numberFieldPrincipalIdele L (σ • x) := by
  apply Units.ext
  exact numberFieldAdeleGaloisMap_algebraMap K L σ x.val

/-- Original finite-component valuations are preserved under simultaneous Galois transport. -/
theorem numberFieldIdeleGaloisMap_finite_valuation (σ : Gal(L/K))
    (a : (AdeleRing (𝓞 L) L)ˣ) (v : HeightOneSpectrum (𝓞 L)) :
    Valued.v (numberFieldIdeleFiniteComponent L (numberFieldGaloisPlaceEquiv K L σ v)
      (numberFieldIdeleGaloisMap K L σ a)).val =
        (Valued.v (numberFieldIdeleFiniteComponent L v a).val : WithZero (Multiplicative ℤ)) := by
  change Valued.v (numberFieldFiniteAdeleGaloisMap K L σ a.val.2
    (numberFieldGaloisPlaceEquiv K L σ v)) = _
  rw [numberFieldFiniteAdeleGaloisMap_apply K L σ _ v _ rfl]
  exact numberFieldGaloisLocalTransport_valuation K L σ v _ rfl (a.val.2 v)

end
end Dubon2026
