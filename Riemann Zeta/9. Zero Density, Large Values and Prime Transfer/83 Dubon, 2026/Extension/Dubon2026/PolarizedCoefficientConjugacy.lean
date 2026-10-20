import Dubon2026.PolarizedCoefficientMap

/-! Genuine coefficient reduction of full polarized strict conjugacy.
This transfers the original residual representation through DUB-17's
actual trace-ring descent. -/

namespace Dubon2026
open Matrix

variable {G ι R k : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing k]

/-- Original coefficient change preserves the actual linear inclusion. -/
theorem polarizedCoefficientMap_linear (f : R →+* k) (U : GeneralLinearGroup ι R) :
    polarizedCoefficientMap f (polarizedLinearInclusion U) =
      polarizedLinearInclusion (GeneralLinearGroup.map f U) := by
  apply SemidirectProduct.ext
  · change (GeneralLinearGroup.map f U, Units.map f.toMonoidHom 1) = (GeneralLinearGroup.map f U, 1)
    rw [map_one]
  · rfl

/-- A genuine residue-one linear conjugator preserves the entire original
polarized residual representation, including its nonidentity component. -/
theorem polarizedStrictConjugate_reduction (f : R →+* k)
    (σ τ : G →* PolarizedGaloisGroup ι R) (W : GeneralLinearGroup ι R)
    (hW : GeneralLinearGroup.map f W = 1)
    (he : ∀ g, σ g = polarizedLinearInclusion W * τ g * (polarizedLinearInclusion W)⁻¹) :
    ∀ g, polarizedCoefficientMap f (σ g) = polarizedCoefficientMap f (τ g) := by
  intro g
  rw [he, map_mul, map_mul, map_inv, polarizedCoefficientMap_linear, hW,
    map_one, one_mul, inv_one, mul_one]

end Dubon2026
