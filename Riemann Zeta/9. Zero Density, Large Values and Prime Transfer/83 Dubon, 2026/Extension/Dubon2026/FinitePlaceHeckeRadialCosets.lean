import Dubon2026.FinitePlaceHeckeRadialDeterminant
import Dubon2026.FinitePlaceGL2ExactDoubleCoset
import Dubon2026.FinitePlaceIntegerUnits

/-! # Exact forward and backward double cosets of the actual original radial Hecke representatives -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- A nonzero original residue representative is not divisible by its original modulus. -/
theorem zmod_nonzero_val_not_dvd (p : ℕ) [NeZero p] (a : ZMod p) (ha : a ≠ 0) :
    ¬(p : ℤ) ∣ (a.val : ℤ) := by
  intro hd
  have hz : (a.val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a.val p).mpr
    (Int.natCast_dvd_natCast.mp hd)
  exact ha ((ZMod.natCast_zmod_val a).symm.trans hz)

/-- The actual Bezout coefficient is a unit modulo the original good prime. -/
theorem heckeBezout_gcdB_not_dvd (N p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N) :
    ¬(p : ℤ) ∣ Int.gcdB p N := by
  intro hd
  have hz : (Int.gcdB p N : ZMod p) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod p) p (Int.gcdB p N)).mpr hd
  exact heckeBezout_upper_ne_zero (Fact.out : p.Prime) hpN (by simp [hz])

/-- Every nonzero original residue term is in the exact next radial Hecke double coset. -/
theorem finitePlaceHeckeRadial_some_forward (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) (n : ℕ) (a : ZMod p) (ha : a ≠ 0) :
    ∃ l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      finitePlaceHeckeRadialMatrix N p hpN (rationalPrimePlace p (Fact.out : p.Prime)) n (some a) =
        l.val * (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
          (finiteAdelicHeckeDiagonal p)) ^ (n + 1) * r.val := by
  obtain ⟨u, hu⟩ := rationalPrimePlace_integer_unit p (Fact.out : p.Prime) (a.val : ℤ)
    (zmod_nonzero_val_not_dvd p a ha)
  refine finitePlaceGL2_unit_entry_hecke_power p (Fact.out : p.Prime) _
    (finitePlaceHeckeRadialMatrix_integral N p hpN _ n (some a)) 0 1 (-u) 1 ?_ (n + 1) ?_
  · rw [finitePlaceHeckeRadialMatrix_some_val]
    change -(a.val : (rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) =
      -((u.val : (rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    exact congrArg Neg.neg (by simpa using hu.symm)
  · simpa only [map_one, one_mul] using finitePlaceHeckeRadialMatrix_det N p hpN _ n (some a)

/-- The genuine Bezout term is also in the exact next radial Hecke double coset. -/
theorem finitePlaceHeckeRadial_none_forward (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) (n : ℕ) :
    ∃ l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      finitePlaceHeckeRadialMatrix N p hpN (rationalPrimePlace p (Fact.out : p.Prime)) n none =
        l.val * (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
          (finiteAdelicHeckeDiagonal p)) ^ (n + 1) * r.val := by
  obtain ⟨u, hu⟩ := rationalPrimePlace_integer_unit p (Fact.out : p.Prime) (Int.gcdB p N)
    (heckeBezout_gcdB_not_dvd N p hpN)
  refine finitePlaceGL2_unit_entry_hecke_power p (Fact.out : p.Prime) _
    (finitePlaceHeckeRadialMatrix_integral N p hpN _ n none) 0 1 u 1 ?_ (n + 1) ?_
  · rw [finitePlaceHeckeRadialMatrix_none_val]
    exact hu.symm
  · simpa only [map_one, one_mul] using finitePlaceHeckeRadialMatrix_det N p hpN _ n none

/-- The original zero-residue term is exactly the preceding radial diagonal times the genuine scalar p. -/
theorem finitePlaceHeckeRadial_some_zero (N p : ℕ) [NeZero N] [NeZero p]
    (hpN : p.Coprime N) (v : HeightOneSpectrum ℤ) (n : ℕ) :
    finitePlaceHeckeRadialMatrix N p hpN v (n + 1) (some 0) =
      GeneralLinearGroup.scalar (Fin 2) (finitePlacePrimeUnit p v) *
        (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p)) ^ n := by
  apply Units.ext
  rw [finitePlaceHeckeRadialMatrix_some_val]
  funext i j
  rw [gl2Scalar_mul_entry, finitePlacePrimeUnit_val, finitePlaceHeckeDiagonal_pow_val]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, mul_comm]

end
end Dubon2026
