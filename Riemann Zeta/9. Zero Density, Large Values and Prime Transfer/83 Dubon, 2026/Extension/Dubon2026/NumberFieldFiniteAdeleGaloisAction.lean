import Dubon2026.NumberFieldFiniteAdeleGaloisMap

/-! # The actual Galois action on the original finite adele ring

Identity and multiplication follow from the proved completed local maps.
This discharges the finite part of the original idele action required for
the equivariant supported sequence in DUB-17's global norm-index route.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The original identity automorphism acts identically on the original finite adeles. -/
theorem numberFieldFiniteAdeleGaloisMap_one (a : FiniteAdeleRing (𝓞 L) L) :
    numberFieldFiniteAdeleGaloisMap K L 1 a = a := by
  apply FiniteAdeleRing.ext
  intro v
  rw [numberFieldFiniteAdeleGaloisMap_apply K L 1 a v v
    (numberFieldGaloisPlaceEquiv_one K L v)]
  exact numberFieldGaloisLocalTransport_one K L v (a v)

/-- Products of original automorphisms compose their original finite-adele maps. -/
theorem numberFieldFiniteAdeleGaloisMap_mul (σ τ : Gal(L/K))
    (a : FiniteAdeleRing (𝓞 L) L) :
    numberFieldFiniteAdeleGaloisMap K L (σ * τ) a =
      numberFieldFiniteAdeleGaloisMap K L σ (numberFieldFiniteAdeleGaloisMap K L τ a) := by
  apply FiniteAdeleRing.ext
  intro w
  let u := (numberFieldGaloisPlaceEquiv K L σ).symm w
  let v := (numberFieldGaloisPlaceEquiv K L τ).symm u
  have hσ : numberFieldGaloisPlaceEquiv K L σ u = w :=
    (numberFieldGaloisPlaceEquiv K L σ).apply_symm_apply w
  have hτ : numberFieldGaloisPlaceEquiv K L τ v = u :=
    (numberFieldGaloisPlaceEquiv K L τ).apply_symm_apply u
  have hστ : numberFieldGaloisPlaceEquiv K L (σ * τ) v = w := by
    rw [numberFieldGaloisPlaceEquiv_mul, hτ, hσ]
  rw [numberFieldFiniteAdeleGaloisMap_apply K L (σ * τ) a v w hστ,
    numberFieldFiniteAdeleGaloisMap_apply K L σ _ u w hσ,
    numberFieldFiniteAdeleGaloisMap_apply K L τ a v u hτ]
  exact numberFieldGaloisLocalTransport_mul K L σ τ v u w hτ hσ hστ (a v)

/-- The original Galois action on the original finite adele ring. -/
@[reducible]
def numberFieldFiniteAdeleGaloisAction : MulSemiringAction Gal(L/K) (FiniteAdeleRing (𝓞 L) L) where
  smul σ a := numberFieldFiniteAdeleGaloisMap K L σ a
  one_smul := numberFieldFiniteAdeleGaloisMap_one K L
  mul_smul := numberFieldFiniteAdeleGaloisMap_mul K L
  smul_zero σ := map_zero (numberFieldFiniteAdeleGaloisMap K L σ)
  smul_add σ := map_add (numberFieldFiniteAdeleGaloisMap K L σ)
  smul_one σ := map_one (numberFieldFiniteAdeleGaloisMap K L σ)
  smul_mul σ := map_mul (numberFieldFiniteAdeleGaloisMap K L σ)

end
end Dubon2026
