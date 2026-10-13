import Dubon2026.NumberFieldGaloisLocalTransport
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-! # The original Galois maps on original finite adeles

The pinned restricted-product map reindexes by the original permutation
of primes and uses the original completed Galois maps. The proved
valuation identity discharges preservation of the integer subrings.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The actual Galois ring map of the original finite adele ring. -/
def numberFieldFiniteAdeleGaloisMap (σ : Gal(L/K)) :
    FiniteAdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom _ _ (numberFieldGaloisPlaceEquiv K L σ).symm
    (numberFieldGaloisPlaceEquiv K L σ).symm.injective.tendsto_cofinite
    (fun w => (numberFieldGaloisLocalTransport K L σ
      ((numberFieldGaloisPlaceEquiv K L σ).symm w) w
      ((numberFieldGaloisPlaceEquiv K L σ).apply_symm_apply w)).toRingHom)
    (Filter.Eventually.of_forall fun w x hx => by
      change Valued.v (numberFieldGaloisLocalTransport K L σ _ w _ x) ≤ 1
      rw [numberFieldGaloisLocalTransport_valuation]
      exact hx)

/-- Each original finite-adele component follows the corresponding original local map. -/
theorem numberFieldFiniteAdeleGaloisMap_apply (σ : Gal(L/K))
    (a : FiniteAdeleRing (𝓞 L) L) (v w : HeightOneSpectrum (𝓞 L))
    (h : numberFieldGaloisPlaceEquiv K L σ v = w) :
    numberFieldFiniteAdeleGaloisMap K L σ a w =
      numberFieldGaloisLocalTransport K L σ v w h (a v) := by
  change numberFieldGaloisLocalTransport K L σ
    ((numberFieldGaloisPlaceEquiv K L σ).symm w) w _
    (a ((numberFieldGaloisPlaceEquiv K L σ).symm w)) = _
  have hc : ∀ (u : HeightOneSpectrum (𝓞 L))
      (hu : numberFieldGaloisPlaceEquiv K L σ u = w),
      numberFieldGaloisLocalTransport K L σ u w hu (a u) =
        numberFieldGaloisLocalTransport K L σ v w h (a v) := by
    intro u hu
    have huv : u = v := (numberFieldGaloisPlaceEquiv K L σ).injective (hu.trans h.symm)
    subst u
    rfl
  exact hc _ _

/-- The original finite-adele map extends the original global automorphism diagonally. -/
theorem numberFieldFiniteAdeleGaloisMap_algebraMap (σ : Gal(L/K)) (x : L) :
    numberFieldFiniteAdeleGaloisMap K L σ
      (algebraMap L (FiniteAdeleRing (𝓞 L) L) x) =
        algebraMap L (FiniteAdeleRing (𝓞 L) L) (σ x) := by
  apply FiniteAdeleRing.ext
  intro w
  rw [numberFieldFiniteAdeleGaloisMap_apply K L σ _
    ((numberFieldGaloisPlaceEquiv K L σ).symm w) w
    ((numberFieldGaloisPlaceEquiv K L σ).apply_symm_apply w)]
  exact numberFieldGaloisLocalTransport_algebraMap K L σ _ w _ x

end
end Dubon2026
