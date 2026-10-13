import Dubon2026.NumberFieldGaloisArchimedeanCoherence
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-! # The actual Galois action on the original infinite adele ring

The original completed transports act on the original product of
archimedean fields. These supply the infinite part of DUB-17's idele action.
-/

namespace Dubon2026
noncomputable section
open NumberField
variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The original Galois ring map on the original infinite adele ring. -/
def numberFieldInfiniteAdeleGaloisMap (σ : Gal(L/K)) : InfiniteAdeleRing L →+* InfiniteAdeleRing L where
  toFun a w := numberFieldGaloisArchimedeanTransport K L σ (σ⁻¹ • w) w (smul_inv_smul σ w)
    (a (σ⁻¹ • w))
  map_one' := funext fun _ => map_one _
  map_zero' := funext fun _ => map_zero _
  map_mul' _ _ := funext fun _ => map_mul _ _ _
  map_add' _ _ := funext fun _ => map_add _ _ _

/-- The actual infinite-adele component follows the corresponding original local transport. -/
theorem numberFieldInfiniteAdeleGaloisMap_apply (σ : Gal(L/K)) (a : InfiniteAdeleRing L)
    (v w : InfinitePlace L) (h : σ • v = w) :
    numberFieldInfiniteAdeleGaloisMap K L σ a w =
      numberFieldGaloisArchimedeanTransport K L σ v w h (a v) := by
  change numberFieldGaloisArchimedeanTransport K L σ (σ⁻¹ • w) w _ (a (σ⁻¹ • w)) = _
  have hc : ∀ (u : InfinitePlace L) (hu : σ • u = w),
      numberFieldGaloisArchimedeanTransport K L σ u w hu (a u) =
        numberFieldGaloisArchimedeanTransport K L σ v w h (a v) := by
    intro u hu
    have huv : u = v := smul_left_cancel σ (hu.trans h.symm)
    subst u
    rfl
  exact hc _ _

/-- The original infinite-adele map agrees with the original diagonal Galois action. -/
theorem numberFieldInfiniteAdeleGaloisMap_algebraMap (σ : Gal(L/K)) (x : L) :
    numberFieldInfiniteAdeleGaloisMap K L σ (algebraMap L (InfiniteAdeleRing L) x) =
      algebraMap L (InfiniteAdeleRing L) (σ x) := by
  funext w
  rw [numberFieldInfiniteAdeleGaloisMap_apply K L σ _ (σ⁻¹ • w) w (smul_inv_smul σ w)]
  exact numberFieldGaloisArchimedeanTransport_algebraMap K L σ _ w _ x

/-- Identity acts identically on the original infinite adele ring. -/
theorem numberFieldInfiniteAdeleGaloisMap_one (a : InfiniteAdeleRing L) :
    numberFieldInfiniteAdeleGaloisMap K L 1 a = a := by
  funext v
  rw [numberFieldInfiniteAdeleGaloisMap_apply K L 1 a v v (one_smul _ v)]
  exact numberFieldGaloisArchimedeanTransport_one K L v (a v)

/-- Products of original automorphisms compose their original infinite-adele maps. -/
theorem numberFieldInfiniteAdeleGaloisMap_mul (σ τ : Gal(L/K)) (a : InfiniteAdeleRing L) :
    numberFieldInfiniteAdeleGaloisMap K L (σ * τ) a =
      numberFieldInfiniteAdeleGaloisMap K L σ (numberFieldInfiniteAdeleGaloisMap K L τ a) := by
  funext w
  let u := σ⁻¹ • w
  let v := τ⁻¹ • u
  have hσ : σ • u = w := smul_inv_smul σ w
  have hτ : τ • v = u := smul_inv_smul τ u
  have hστ : (σ * τ) • v = w := by rw [mul_smul, hτ, hσ]
  rw [numberFieldInfiniteAdeleGaloisMap_apply K L (σ * τ) a v w hστ,
    numberFieldInfiniteAdeleGaloisMap_apply K L σ _ u w hσ,
    numberFieldInfiniteAdeleGaloisMap_apply K L τ a v u hτ]
  exact numberFieldGaloisArchimedeanTransport_mul K L σ τ v u w hτ hσ hστ (a v)

/-- The original Galois action on the original infinite adele ring. -/
@[reducible]
def numberFieldInfiniteAdeleGaloisAction : MulSemiringAction Gal(L/K) (InfiniteAdeleRing L) where
  smul σ a := numberFieldInfiniteAdeleGaloisMap K L σ a
  one_smul := numberFieldInfiniteAdeleGaloisMap_one K L
  mul_smul := numberFieldInfiniteAdeleGaloisMap_mul K L
  smul_zero σ := map_zero (numberFieldInfiniteAdeleGaloisMap K L σ)
  smul_add σ := map_add (numberFieldInfiniteAdeleGaloisMap K L σ)
  smul_one σ := map_one (numberFieldInfiniteAdeleGaloisMap K L σ)
  smul_mul σ := map_mul (numberFieldInfiniteAdeleGaloisMap K L σ)

end
end Dubon2026
