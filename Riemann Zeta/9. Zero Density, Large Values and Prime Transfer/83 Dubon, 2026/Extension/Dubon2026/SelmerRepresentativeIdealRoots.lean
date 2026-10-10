import Dubon2026.PrincipalIdealValuationBridge

/-! # Actual ideal roots of original empty-set Selmer representatives -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The original field units whose actual power classes lie in the empty-set Selmer group. -/
abbrev EmptySelmerRepresentativeUnits (n : ℕ) : Subgroup Kˣ :=
  (IsDedekindDomain.selmerGroup (R := R) (K := K) (S := ∅) (n := n)).comap
    (QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range)

/-- The actual divided-multiplicity ideal root of an original Selmer representative. -/
def emptySelmerRepresentativeIdealRoot (n : ℕ)
    (x : EmptySelmerRepresentativeUnits (R := R) (K := K) n) :
    (FractionalIdeal R⁰ K)ˣ :=
  fractionalIdealCountRootUnit n (toPrincipalIdeal R K x.val)

/-- The genuine root retains the exact original principal ideal as its nth power. -/
theorem emptySelmerRepresentativeIdealRoot_pow (n : ℕ)
    (x : EmptySelmerRepresentativeUnits (R := R) (K := K) n) :
    emptySelmerRepresentativeIdealRoot n x ^ n = toPrincipalIdeal R K x.val :=
  fractionalIdealCountRootUnit_pow n (toPrincipalIdeal R K x.val)
    ((emptySelmer_mem_iff_principal_counts n x.val).mp x.property)

/-- The actual original fractional-ideal unit group has injective positive powers. -/
theorem fractionalIdealUnits_pow_injective (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (fun I : (FractionalIdeal R⁰ K)ˣ => I ^ n) := by
  intro I J h
  apply Units.ext
  apply fractionalIdeal_eq_of_pow_eq I.ne_zero J.ne_zero n hn
  exact congrArg Units.val h

/-- The actual root of the original identity representative is the identity fractional ideal. -/
theorem emptySelmerRepresentativeIdealRoot_one (n : ℕ) (hn : n ≠ 0) :
    emptySelmerRepresentativeIdealRoot (R := R) (K := K) n 1 = 1 := by
  apply fractionalIdealUnits_pow_injective n hn
  dsimp only
  rw [emptySelmerRepresentativeIdealRoot_pow, one_pow]
  exact map_one (toPrincipalIdeal R K)

/-- The actual ideal root multiplies exactly on original Selmer representatives. -/
theorem emptySelmerRepresentativeIdealRoot_mul (n : ℕ) (hn : n ≠ 0)
    (x y : EmptySelmerRepresentativeUnits (R := R) (K := K) n) :
    emptySelmerRepresentativeIdealRoot n (x * y) =
      emptySelmerRepresentativeIdealRoot n x * emptySelmerRepresentativeIdealRoot n y := by
  apply fractionalIdealUnits_pow_injective n hn
  dsimp only
  rw [mul_pow, emptySelmerRepresentativeIdealRoot_pow,
    emptySelmerRepresentativeIdealRoot_pow, emptySelmerRepresentativeIdealRoot_pow]
  exact map_mul (toPrincipalIdeal R K) x.val y.val

/-- Original Selmer representatives map homomorphically to their genuine fractional-ideal roots. -/
def emptySelmerRepresentativeIdealRootHom (n : ℕ) (hn : n ≠ 0) :
    EmptySelmerRepresentativeUnits (R := R) (K := K) n →* (FractionalIdeal R⁰ K)ˣ where
  toFun := emptySelmerRepresentativeIdealRoot n
  map_one' := emptySelmerRepresentativeIdealRoot_one n hn
  map_mul' := emptySelmerRepresentativeIdealRoot_mul n hn

/-- For an original representative that is itself a field-unit nth power, the actual root is the corresponding original principal ideal. -/
theorem emptySelmerRepresentativeIdealRoot_of_power (n : ℕ) (hn : n ≠ 0)
    (x : EmptySelmerRepresentativeUnits (R := R) (K := K) n)
    (y : Kˣ) (hxy : x.val = y ^ n) :
    emptySelmerRepresentativeIdealRoot n x = toPrincipalIdeal R K y := by
  apply fractionalIdealUnits_pow_injective n hn
  dsimp only
  rw [emptySelmerRepresentativeIdealRoot_pow, hxy, map_pow]

end
end Dubon2026
