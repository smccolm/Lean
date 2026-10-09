import Dubon2026.LocalInducedHeckeEigenvalue

/-! # The exact normalized intrinsic Hecke value on the original principal-series spherical line -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original normalization transforms the genuine inverse-diagonal coset sum into the precise inverse-Satake trace. -/
theorem normalizedLocalHecke_value (p : ℕ) (hp : p.Prime) (α β : ℂˣ) :
    (p : ℂ) * (((α * finitePlaceSqrtResidueUnit (rationalPrimePlace p hp))⁻¹ : ℂˣ) : ℂ) +
      (((β * (finitePlaceSqrtResidueUnit (rationalPrimePlace p hp))⁻¹)⁻¹ : ℂˣ) : ℂ) =
    (Real.sqrt p : ℂ) * (((α⁻¹ : ℂˣ) : ℂ) + (β⁻¹ : ℂˣ)) := by
  have hs : (Real.sqrt p : ℂ) ^ 2 = p := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  have hs0 : (Real.sqrt p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.pos)))
  simp only [Units.val_inv_eq_inv_val, Units.val_mul, finitePlaceSqrtResidueUnit_val,
    rationalPrimePlace_natGenerator]
  rw [← hs]
  field_simp [hs0]

/-- The genuine normalized local principal series has its precise original inverse-Satake Hecke eigenvalue on the actual spherical section. -/
theorem normalizedLocalPrincipal_hecke_eigenvalue (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β : ℂˣ) :
    finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p)
      (normalizedLocalPrincipalRepresentation (rationalPrimePlace p (Fact.out : p.Prime)) α β)
      (finitePlaceInducedSpherical (rationalPrimePlace p (Fact.out : p.Prime))
        (α * finitePlaceSqrtResidueUnit (rationalPrimePlace p (Fact.out : p.Prime)))
        (β * (finitePlaceSqrtResidueUnit (rationalPrimePlace p (Fact.out : p.Prime)))⁻¹)) =
    ((Real.sqrt p : ℂ) * (((α⁻¹ : ℂˣ) : ℂ) + (β⁻¹ : ℂˣ))) •
      finitePlaceInducedSpherical (rationalPrimePlace p (Fact.out : p.Prime))
        (α * finitePlaceSqrtResidueUnit (rationalPrimePlace p (Fact.out : p.Prime)))
        (β * (finitePlaceSqrtResidueUnit (rationalPrimePlace p (Fact.out : p.Prime)))⁻¹) := by
  have he := finitePlaceInducedSpherical_hecke_eigenvalue p
    (α * finitePlaceSqrtResidueUnit (rationalPrimePlace p (Fact.out : p.Prime)))
    (β * (finitePlaceSqrtResidueUnit (rationalPrimePlace p (Fact.out : p.Prime)))⁻¹)
  rw [normalizedLocalHecke_value] at he
  exact he

/-- Determinant-one original parameters identify the inverse-Satake trace with the original Satake trace. -/
theorem localSatake_inverse_trace (α β : ℂˣ) (hαβ : α * β = 1) :
    ((α⁻¹ : ℂˣ) : ℂ) + (β⁻¹ : ℂˣ) = (α : ℂ) + (β : ℂ) := by
  have hβ : β = α⁻¹ := eq_inv_of_mul_eq_one_right hαβ
  rw [hβ, inv_inv, add_comm]

end
end Dubon2026
