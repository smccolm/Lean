import Dubon2026.LocalResidueRootSeparation
import Mathlib.Algebra.Group.Commute.Units

/-! DUB-17/18 -> residual Galois association -> the boundary character
branch. The existing native root-separation theorem identifies the actual
local Frobenius and inertia actions on roots of order prime to the residue
characteristic. No auxiliary valuation-ring model is introduced.
-/
namespace Dubon2026
noncomputable section

/-- Equal residues identify two roots of the same invertible order in the
actual local domain. -/
theorem sourceLocal_roots_eq_of_residue_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {u v : R} {n : ℕ} (hu : u ^ n = 1) (hv : v ^ n = 1)
    (hn : (n : IsLocalRing.ResidueField R) ≠ 0)
    (he : IsLocalRing.residue R u = IsLocalRing.residue R v) : u = v := by
  have hn0 : n ≠ 0 := by intro h; subst n; exact hn (Nat.cast_zero)
  obtain ⟨u, rfl⟩ := IsUnit.of_pow_eq_one hu hn0
  obtain ⟨v, rfl⟩ := IsUnit.of_pow_eq_one hv hn0
  have hp : ((u * v⁻¹ : Rˣ) : R) ^ n = 1 := by
    rw [Units.val_mul, mul_pow, hu, one_mul, ← Units.val_pow_eq_pow_val]
    have hv' : v ^ n = 1 := Units.ext hv
    rw [inv_pow, hv', inv_one, Units.val_one]
  have hr : IsLocalRing.residue R ((u * v⁻¹ : Rˣ) : R) = 1 := by
    rw [Units.val_mul, map_mul, he, ← map_mul, Units.mul_inv, map_one]
  have h := local_eq_one_of_residue_eq_one_of_pow_eq_one hp hn hr
  have h' : u * v⁻¹ = 1 := Units.ext h
  exact congrArg Units.val (mul_inv_eq_one.mp h')

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L]
  [CompleteSpace K] [IsGalois K L]

attribute [local instance] algebraicLocalIntegerAction

/-- An actual arithmetic residue Frobenius acts by the same power on every
root whose order is invertible in the original residue field. -/
theorem sourceLocal_frobenius_root
    (n q : ℕ) (hn : n ≠ 0)
    (hnr : (n : IsLocalRing.ResidueField (algebraicLocalIntegerRing L)) ≠ 0)
    (g : Gal(L/K))
    (hg : ∀ x : IsLocalRing.ResidueField (algebraicLocalIntegerRing L),
      g • x = x ^ q) (ζ : L) (hζ : ζ ^ n = 1) : g ζ = ζ ^ q := by
  let R := algebraicLocalIntegerRing L
  have hzR : ζ ∈ R := by
    change ‖ζ‖₊ ≤ 1
    have he : ‖ζ‖₊ ^ n = 1 := by rw [← nnnorm_pow, hζ, nnnorm_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le' hn).mp he).le
  let z : R := ⟨ζ, hzR⟩
  have hz : z ^ n = 1 := Subtype.ext hζ
  have hgz : (g • z) ^ n = 1 := by rw [← smul_pow', hz, smul_one]
  have hqz : (z ^ q) ^ n = 1 := by rw [← pow_mul, mul_comm q n, pow_mul, hz, one_pow]
  have he : IsLocalRing.residue R (g • z) = IsLocalRing.residue R (z ^ q) := by
    rw [IsLocalRing.ResidueField.residue_smul, hg, map_pow]
  exact congrArg Subtype.val (sourceLocal_roots_eq_of_residue_eq hgz hqz hnr he)

/-- Original norm inertia fixes every root of order prime to the residue
characteristic. -/
theorem sourceLocal_inertia_root
    (n : ℕ) (hn : n ≠ 0)
    (hnr : (n : IsLocalRing.ResidueField (algebraicLocalIntegerRing L)) ≠ 0)
    (g : Gal(L/K)) (hg : g ∈ algebraicLocalInertia K L)
    (ζ : L) (hζ : ζ ^ n = 1) : g ζ = ζ := by
  have h := sourceLocal_frobenius_root K L n 1 hn hnr g
    (fun x => by simpa only [pow_one] using
      (algebraicLocalInertia_mem_iff K L g).mp hg x) ζ hζ
  simpa only [pow_one] using h

end
end Dubon2026
