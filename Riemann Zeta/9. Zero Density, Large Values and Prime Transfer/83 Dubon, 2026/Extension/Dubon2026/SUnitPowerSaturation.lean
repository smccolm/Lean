import Dubon2026.SUnitPowerTorsion

/-! # Actual S-units are saturated under nonzero powers

An nth root in the original base field of an S-unit is itself an S-unit.
This identifies the original S-unit power quotient with its actual image
inside the field power quotient, as required by global Kummer preparation
and the norm-index dependency of DUB-17.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Actual S-unit membership is reflected by every nonzero power in the original field. -/
theorem unit_mem_sUnit_of_pow_mem (S : Set (HeightOneSpectrum R))
    (x : Kˣ) (n : ℕ) (hn : n ≠ 0) (hx : x ^ n ∈ S.unit K) : x ∈ S.unit K := by
  intro v hv
  have hp : (v.valuationOfNeZero x) ^ n = 1 := by
    apply WithZero.coe_injective
    rw [← map_pow, HeightOneSpectrum.valuationOfNeZero_eq, WithZero.coe_one]
    exact hx v hv
  have hz : (n : ℤ) * (v.valuationOfNeZero x).toAdd = 0 := by
    have h := congrArg Multiplicative.toAdd hp
    change n • (v.valuationOfNeZero x).toAdd = 0 at h
    simpa only [nsmul_eq_mul] using h
  have hv' : v.valuationOfNeZero x = 1 :=
    congrArg Multiplicative.ofAdd
      ((mul_eq_zero.mp hz).resolve_left (Int.natCast_ne_zero.mpr hn))
  have h := congrArg (fun z : Multiplicative ℤ => (z : WithZero (Multiplicative ℤ))) hv'
  simpa only [HeightOneSpectrum.valuationOfNeZero_eq, WithZero.coe_one] using h

/-- An original S-unit is an nth power among S-units exactly when it is an nth power in K. -/
theorem sUnit_mem_power_range_iff (S : Set (HeightOneSpectrum R))
    (n : ℕ) (hn : n ≠ 0) (x : S.unit K) :
    x ∈ (powMonoidHom (α := S.unit K) n).range ↔
      x.val ∈ (powMonoidHom (α := Kˣ) n).range := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.val, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    change y ^ n = x.val at hy
    have hymem : y ^ n ∈ S.unit K := hy.symm ▸ x.property
    exact ⟨⟨y, unit_mem_sUnit_of_pow_mem S y n hn hymem⟩, Subtype.ext hy⟩

end
end Dubon2026
