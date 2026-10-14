import Dubon2026.RationalPrimeWittCyclotomicAlgebra
import Dubon2026.PrimeChangedPolynomialMap

/-! # The primitive equation over the literal original completion

Transport the already proved primitive polynomial through the actual
original coefficient embeddings. Irreducibility over the larger Witt
fraction field implies irreducibility over the original completion.
The actual evaluated point is therefore algebraic of the exact required
degree over that original field, giving a direct finite auxiliary-field
construction for DUB-17 without a general descent infrastructure.
-/
namespace Dubon2026
noncomputable section
open Polynomial
open scoped ValuativeRel
attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower

/-- The exact original changed polynomial maps to the proved Witt primitive polynomial. -/
theorem rationalPrimeChangedPolynomial_map (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
    (primeChangedPrimitivePolynomial q ((a : rationalPrimeLocalField p hp) * q) n).map
      (algebraMap _ (rationalPrimeWittField p hp)) =
    (primeChangedPrimitivePolynomial q (v.val * q) n).map
      (algebraMap _ (rationalPrimeWittField p hp)) := by
  dsimp only
  rw [primeChangedPrimitivePolynomial_map, primeChangedPrimitivePolynomial_map]
  apply congrArg (fun π => primeChangedPrimitivePolynomial _ π n)
  have hv : (Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u).val = a := by
    change rationalPrimeIntegerWittMap p hp u.val = a
    rw [hu, map_natCast]
  rw [hv, map_mul, map_natCast, map_natCast, map_mul, map_natCast, map_natCast]

/-- The primitive changed polynomial is irreducible over the literal original completion. -/
theorem rationalPrimeChangedPolynomial_irreducible (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    Irreducible (primeChangedPrimitivePolynomial q ((a : rationalPrimeLocalField p hp) * q) n) := by
  dsimp only
  apply Polynomial.Monic.irreducible_of_irreducible_map (algebraMap _ (rationalPrimeWittField p hp))
    _ (primeChangedPrimitivePolynomial_monic _ _ _)
  rw [rationalPrimeChangedPolynomial_map p hp n a u hu]
  exact wittCyclotomicChangedPolynomial_irreducible _ _ n

/-- The actual evaluated point satisfies the exact primitive polynomial over the original completion. -/
theorem rationalPrimeChangedFieldPoint_aeval (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
    aeval (wittCyclotomicChangedFieldPoint q v n)
      (primeChangedPrimitivePolynomial q ((a : rationalPrimeLocalField p hp) * q) n) = 0 := by
  dsimp only
  rw [← Polynomial.aeval_map_algebraMap (A := rationalPrimeWittField p hp),
    rationalPrimeChangedPolynomial_map p hp n a u hu]
  apply wittCyclotomicChangedFieldPoint_aeval _ _ n a
  · change rationalPrimeIntegerWittMap p hp u.val = a
    rw [hu, map_natCast]
  · simpa only [rationalPrimePlace_natGenerator] using ha

/-- The minimal polynomial over the original completion is exactly the original changed primitive polynomial. -/
theorem rationalPrimeChangedFieldPoint_minpoly (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
    minpoly (rationalPrimeLocalField p hp) (wittCyclotomicChangedFieldPoint q v n) =
      primeChangedPrimitivePolynomial q ((a : rationalPrimeLocalField p hp) * q) n := by
  dsimp only
  have h := minpoly.eq_of_irreducible (rationalPrimeChangedPolynomial_irreducible p hp n a u hu)
    (rationalPrimeChangedFieldPoint_aeval p hp n a u hu ha)
  rw [(primeChangedPrimitivePolynomial_monic _ _ _).leadingCoeff,
    inv_one, Polynomial.C_1, mul_one] at h
  exact h.symm

end
end Dubon2026
