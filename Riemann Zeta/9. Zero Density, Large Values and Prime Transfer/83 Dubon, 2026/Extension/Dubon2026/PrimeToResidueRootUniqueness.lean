import Dubon2026.LocalUnitPowerResidueInjectivity

/-! # Original prime-to-residue roots are determined by reduction

Apply the existing geometric-sum root detection to the ratio of the two
original unit roots. This lifts the actual residue Frobenius formula and
supplies the unramified local terms in DUB-17's cyclotomic principal product.
-/
namespace Dubon2026
noncomputable section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

/-- Original unit roots of order invertible in the residue field agree if their actual reductions agree. -/
theorem primeToResidue_unit_roots_eq {n : ℕ}
    (hn : (n : IsLocalRing.ResidueField R) ≠ 0) (x y : Rˣ)
    (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hxy : IsLocalRing.residue R (x : R) = IsLocalRing.residue R (y : R)) : x = y := by
  have hnu : IsUnit (n : R) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    (by simpa only [map_natCast] using hn)
  have hp : (x * y⁻¹) ^ n = 1 := by simp only [mul_pow, inv_pow, hx, hy, inv_one, mul_one]
  have hr : Units.map (IsLocalRing.residue R).toMonoidHom (x * y⁻¹) = 1 := by
    have he : Units.map (IsLocalRing.residue R).toMonoidHom x =
        Units.map (IsLocalRing.residue R).toMonoidHom y := Units.ext hxy
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hz : x * y⁻¹ = 1 := by
    apply Units.ext
    apply localRing_unitExponent_root_eq_one n hnu
    · have h := congrArg (fun u : Rˣ => (u : R)) hp
      simpa using h
    · exact congrArg (fun u : (IsLocalRing.ResidueField R)ˣ => (u : IsLocalRing.ResidueField R)) hr
  exact mul_inv_eq_one.mp hz

end
end Dubon2026
