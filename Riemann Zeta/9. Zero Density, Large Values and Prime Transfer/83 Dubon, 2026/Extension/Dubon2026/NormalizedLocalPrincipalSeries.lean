import Dubon2026.FinitePlaceSphericalInduced
import Dubon2026.AdelicRealScalar

/-! # The actual normalized unramified principal series over the original rational local field -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The genuine positive square root of the original residue characteristic, as a nonzero complex unit. -/
def finitePlaceSqrtResidueUnit (v : HeightOneSpectrum ℤ) : ℂˣ :=
  Units.mk0 (Real.sqrt (Rat.HeightOneSpectrum.natGenerator v) : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr
      (Nat.cast_pos.mpr (Rat.HeightOneSpectrum.prime_natGenerator v).pos))))

/-- The literal positive square-root factor in the actual local normalization. -/
theorem finitePlaceSqrtResidueUnit_val (v : HeightOneSpectrum ℤ) :
    (finitePlaceSqrtResidueUnit v).val = (Real.sqrt (Rat.HeightOneSpectrum.natGenerator v) : ℂ) := rfl

/-- The original normalized lower-Borel induction with parameters alpha and beta. Its actual modulus half-factor is represented by the opposite square-root shifts on the two original diagonal orders. -/
abbrev NormalizedLocalPrincipalSeries (v : HeightOneSpectrum ℤ) (α β : ℂˣ) :=
  FinitePlaceInducedSpace v (α * finitePlaceSqrtResidueUnit v) (β * (finitePlaceSqrtResidueUnit v)⁻¹)

/-- The genuine right-translation representation on the actual normalized principal-series function space. -/
def normalizedLocalPrincipalRepresentation (v : HeightOneSpectrum ℤ) (α β : ℂˣ) :
    Representation ℂ (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
      (NormalizedLocalPrincipalSeries v α β) :=
  smoothInducedCharacterRepresentation _ (finitePlaceLowerCharacter v
    (α * finitePlaceSqrtResidueUnit v) (β * (finitePlaceSqrtResidueUnit v)⁻¹))

/-- An actual local scalar matrix belongs to the genuine original lower Borel. -/
def gl2LowerScalar {F : Type*} [Field F] (u : Fˣ) : gl2UpperZeroSubgroup F :=
  ⟨GeneralLinearGroup.scalar (Fin 2) u, by
    change (GeneralLinearGroup.scalar (Fin 2) u).val 0 1 = 0
    simp [GeneralLinearGroup.scalar, Matrix.scalar]⟩

/-- Both original diagonal characters of a genuine scalar recover the original local unit exactly. -/
theorem gl2LowerDiagonalHom_scalar {F : Type*} [Field F] (i : Fin 2) (u : Fˣ) :
    gl2LowerDiagonalHom i (gl2LowerScalar u) = u := by
  apply Units.ext
  fin_cases i <;> simp [gl2LowerDiagonalHom, gl2LowerScalar, GeneralLinearGroup.scalar, Matrix.scalar]

/-- The actual lower-Borel character has its exact scalar value in the product of the two original unramified parameters. -/
theorem finitePlaceLowerCharacter_scalar (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (u : (v.adicCompletion ℚ)ˣ) :
    finitePlaceLowerCharacter v z₁ z₂ (gl2LowerScalar u) =
      (((z₁ * z₂) ^ finitePlaceUnitOrder v u : ℂˣ) : ℂ) := by
  change ((finitePlaceUnramifiedCharacter v z₁ (gl2LowerDiagonalHom 0 (gl2LowerScalar u)) *
    finitePlaceUnramifiedCharacter v z₂ (gl2LowerDiagonalHom 1 (gl2LowerScalar u)) : ℂˣ) : ℂ) = _
  rw [gl2LowerDiagonalHom_scalar, gl2LowerDiagonalHom_scalar]
  change ((z₁ ^ finitePlaceUnitOrder v u * z₂ ^ finitePlaceUnitOrder v u : ℂˣ) : ℂ) = _
  rw [mul_zpow]

/-- Determinant-one Satake parameters give the actual trivial central action on every vector of the genuine normalized local principal series. -/
theorem normalizedLocalPrincipalRepresentation_scalar (v : HeightOneSpectrum ℤ) (α β : ℂˣ)
    (hαβ : α * β = 1) (u : (v.adicCompletion ℚ)ˣ)
    (f : NormalizedLocalPrincipalSeries v α β) :
    normalizedLocalPrincipalRepresentation v α β (GeneralLinearGroup.scalar (Fin 2) u) f = f := by
  have he : (α * finitePlaceSqrtResidueUnit v) * (β * (finitePlaceSqrtResidueUnit v)⁻¹) = 1 := by
    calc
      _ = (α * β) * (finitePlaceSqrtResidueUnit v * (finitePlaceSqrtResidueUnit v)⁻¹) := by ac_rfl
      _ = 1 := by rw [hαβ, mul_inv_cancel, one_mul]
  apply Subtype.ext
  funext g
  change f.val (g * GeneralLinearGroup.scalar (Fin 2) u) = f.val g
  rw [← gl2Scalar_mul_comm]
  have hf := f.property.1 (gl2LowerScalar u) g
  rw [finitePlaceLowerCharacter_scalar, he, one_zpow, Units.val_one, one_mul] at hf
  exact hf

end
end Dubon2026
