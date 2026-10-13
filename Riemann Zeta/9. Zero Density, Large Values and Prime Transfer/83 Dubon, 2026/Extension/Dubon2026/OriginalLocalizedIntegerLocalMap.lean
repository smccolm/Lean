import Dubon2026.OriginalIntegerLocalValuationMap

/-! # The original localized integers map to the actual local valuation ring

Only invertibility of the original exceptional integer is needed. At the
required rational primes this will come from the existing local integer-unit
theorem. The exact map permits reuse of unramified base change for DUB-17.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

variable (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E] [ValuativeRel E]
  (a : 𝓞 K) (ha : a ≠ 0) (hu : IsUnit (originalIntegerToValuationIntegerMap K E a))

/-- Localize the genuine integer map at the original exceptional element. -/
def originalLocalizedIntegerToValuationIntegerMap : originalLocalizedIntegers K a ha →+* 𝒪[E] :=
  IsLocalization.Away.lift a hu

/-- The actual localized integer map retains the original field embedding
on every fraction, rather than just on the original integer generators. -/
theorem originalLocalizedIntegerToValuationIntegerMap_coe (x : originalLocalizedIntegers K a ha) :
    (originalLocalizedIntegerToValuationIntegerMap K E a ha hu x : E) = algebraMap K E (x : K) := by
  have he : (algebraMap 𝒪[E] E).comp (originalLocalizedIntegerToValuationIntegerMap K E a ha hu) =
      (algebraMap K E).comp (originalLocalizedIntegers K a ha).val.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext z
    change (IsLocalization.Away.lift a hu (algebraMap (𝓞 K) (originalLocalizedIntegers K a ha) z) : E) =
      algebraMap K E (z : K)
    rw [IsLocalization.Away.lift_eq]
    rfl
  exact DFunLike.congr_fun he x

end
end Dubon2026
