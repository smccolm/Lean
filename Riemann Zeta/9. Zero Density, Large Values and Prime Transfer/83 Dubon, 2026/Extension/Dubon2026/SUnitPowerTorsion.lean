import Dubon2026.SUnitValuationKernel
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Actual power torsion in the original S-unit group

Every root of unity has valuation one, so the nth-power kernel of the
original S-units is precisely the original field's roots of unity. This
discharges the torsion factor in the global S-unit power-index calculation.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- An actual field unit of nonzero finite order is an S-unit for every original S. -/
theorem unit_mem_sUnit_of_pow_eq_one (S : Set (HeightOneSpectrum R))
    (x : Kˣ) (n : ℕ) (hn : n ≠ 0) (hx : x ^ n = 1) : x ∈ S.unit K := by
  intro v _
  have hp : (v.valuationOfNeZero x) ^ n = 1 := by
    rw [← map_pow, hx, map_one]
  have hz : (n : ℤ) * (v.valuationOfNeZero x).toAdd = 0 := by
    have h := congrArg Multiplicative.toAdd hp
    change n • (v.valuationOfNeZero x).toAdd = 0 at h
    simpa only [nsmul_eq_mul] using h
  have hz' := (mul_eq_zero.mp hz).resolve_left (Int.natCast_ne_zero.mpr hn)
  have hv : v.valuationOfNeZero x = 1 := congrArg Multiplicative.ofAdd hz'
  have h := congrArg (fun z : Multiplicative ℤ => (z : WithZero (Multiplicative ℤ))) hv
  simpa only [HeightOneSpectrum.valuationOfNeZero_eq, WithZero.coe_one] using h

/-- The original S-unit nth-power kernel identifies with all actual field roots of unity. -/
def sUnitPowerKernelEquivRoots (S : Set (HeightOneSpectrum R)) (n : ℕ) (hn : n ≠ 0) :
    (powMonoidHom (α := S.unit K) n).ker ≃* rootsOfUnity n K where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, unit_mem_sUnit_of_pow_eq_one S x.val n hn x.property⟩,
    Subtype.ext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- A primitive nth root gives exactly n elements in the actual S-unit power kernel. -/
theorem sUnitPowerKernel_card (S : Set (HeightOneSpectrum R))
    (n : ℕ) (hn : n ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (powMonoidHom (α := S.unit K) n).ker = n := by
  letI : NeZero n := ⟨hn⟩
  rw [Nat.card_congr (sUnitPowerKernelEquivRoots S n hn).toEquiv,
    Nat.card_eq_fintype_card]
  exact hζ.card_rootsOfUnity

end
end Dubon2026
