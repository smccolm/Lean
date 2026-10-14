/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted for the original Dubon coefficient route from
Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerCoefficient.lean at
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. The Apache 2.0 license is retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/

import Dubon2026.PrimeWittFrobeniusRotation
import Dubon2026.RationalPrimeOriginalResidueCard
import Mathlib.RingTheory.WittVector.Compare

/-! # The original rational prime integer ring in the completed-unramified Witt coefficients

Use the actual prime completion integer equivalence and pinned Witt/p-adic
integer equivalence to map the original valuation integers into the actual
Witt ring over an algebraic closure of its prime residue field. Frobenius
fixes this original base image, and the required unit rotation is constructed.
This discharges the linear coefficient existence step for the changed
uniformizer used in DUB-17's ramified cyclotomic reciprocity formula.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance 1100] Ring.toIntAlgebra

/-- The positive generator of the original finite prime is prime. -/
local instance rationalPrimeWittPrime (p : ℕ) (hp : p.Prime) :
    Fact (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)).Prime :=
  ⟨Rat.HeightOneSpectrum.prime_natGenerator _⟩

/-- The actual original valuation integers map into the Witt coefficients through their genuine integer-ring equivalences. -/
def rationalPrimeIntegerWittMap (p : ℕ) (hp : p.Prime) :
    𝒪[rationalPrimeLocalField p hp] →+*
      WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
        (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))) :=
  let v := rationalPrimePlace p hp
  let q := Rat.HeightOneSpectrum.natGenerator v
  let e₁ : 𝒪[rationalPrimeLocalField p hp] ≃+* rationalPrimeLocalIntegerRing p hp :=
    RingEquiv.subringCongr (rationalPrimeLocalInteger_subring_eq p hp)
  let e₂ := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  (WittVector.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).comp
    (((WittVector.equiv q).symm.toRingHom).comp (e₁.trans e₂).toRingHom)

/-- Actual Witt Frobenius fixes the original rational local integer image. -/
theorem rationalPrimeIntegerWittMap_frobenius (p : ℕ) (hp : p.Prime)
    (z : 𝒪[rationalPrimeLocalField p hp]) :
    WittVector.frobenius (rationalPrimeIntegerWittMap p hp z) =
      rationalPrimeIntegerWittMap p hp z := by
  apply WittVector.ext
  intro k
  simp only [rationalPrimeIntegerWittMap, RingHom.comp_apply,
    WittVector.coeff_frobenius_charP, WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

/-- Every original rational local integer unit supplies an actual invertible coefficient with the required Frobenius multiplier; no rotation witness is assumed. -/
theorem rationalPrimeIntegerWittMap_exists_rotation (p : ℕ) (hp : p.Prime)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    ∃ ε : (WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
        (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))))ˣ,
      WittVector.frobenius ε.val = ε.val * rationalPrimeIntegerWittMap p hp u.val := by
  exact primeWitt_exists_frobenius_unit_rotation _
    (Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u)

end
end Dubon2026
