import Dubon2026.OriginalIdeleGaloisTower

/-! # The original idele action after restricting scalars

The same field automorphism acts on the same original adeles independently
of its displayed fixed field. The literal equality below is used when the
restriction kernel partitions the original norm in a tower; this serves
the cyclic norm-index and coprime descent dependencies of DUB-17.
-/
namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField
variable (K E L : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]

/-- Restriction of scalars keeps the actual original idele action unchanged. -/
theorem numberFieldIdeleGaloisMap_restrictScalars (σ : Gal(L/E))
    (a : (AdeleRing (𝓞 L) L)ˣ) :
    numberFieldIdeleGaloisMap K L (σ.restrictScalars K) a =
      numberFieldIdeleGaloisMap E L σ a := rfl

/-- Restriction of scalars keeps the actual original class action unchanged. -/
theorem numberFieldIdeleClassGaloisMap_restrictScalars (σ : Gal(L/E))
    (a : OriginalNumberFieldIdeleClassGroup L) :
    numberFieldIdeleClassGaloisMap K L (σ.restrictScalars K) a =
      numberFieldIdeleClassGaloisMap E L σ a := rfl

end
end Dubon2026
