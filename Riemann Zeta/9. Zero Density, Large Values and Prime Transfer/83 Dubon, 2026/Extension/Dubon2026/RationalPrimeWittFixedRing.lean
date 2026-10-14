/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The fixed-ring proof is adapted to the original rational valuation integers
from Nyll/ClassFieldTheory/LubinTate/Padic/CompletedUnramifiedFrobeniusFixed.lean
at dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. Apache 2.0 license retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/
import Dubon2026.RationalPrimeWittCoefficient
import Mathlib.FieldTheory.Finite.Basic

/-! # Exact original integer descent of Frobenius-fixed Witt coefficients

The coefficient map is injective, and its image is exactly the Frobenius
fixed ring. This is the coefficient descent required to prove finiteness
of the actual changed-uniformizer fixed field, then its normed uniformizer
and DUB-17's ramified reciprocity formula. No fixed-ring claim is assumed.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance 1100] Ring.toIntAlgebra
attribute [local instance] rationalPrimeWittPrime

/-- The actual original integer-to-Witt coefficient map is injective. -/
theorem rationalPrimeIntegerWittMap_injective (p : ℕ) (hp : p.Prime) :
    Function.Injective (rationalPrimeIntegerWittMap p hp) := by
  let v := rationalPrimePlace p hp
  let q := Rat.HeightOneSpectrum.natGenerator v
  let e₁ : 𝒪[rationalPrimeLocalField p hp] ≃+* rationalPrimeLocalIntegerRing p hp :=
    RingEquiv.subringCongr (rationalPrimeLocalInteger_subring_eq p hp)
  let e₂ := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  exact (WittVector.map_injective
    (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) (RingHom.injective _)).comp
      ((WittVector.equiv q).symm.injective.comp (e₁.trans e₂).injective)

/-- Witt Frobenius fixes exactly the image of the actual original rational prime valuation integers. -/
theorem rationalPrimeIntegerWittMap_frobenius_fixed_iff
    (p : ℕ) (hp : p.Prime)
    (x : WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
      (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))))) :
    WittVector.frobenius x = x ↔
      ∃ z : 𝒪[rationalPrimeLocalField p hp], rationalPrimeIntegerWittMap p hp z = x := by
  let v := rationalPrimePlace p hp
  let q := Rat.HeightOneSpectrum.natGenerator v
  let e₁ : 𝒪[rationalPrimeLocalField p hp] ≃+* rationalPrimeLocalIntegerRing p hp :=
    RingEquiv.subringCongr (rationalPrimeLocalInteger_subring_eq p hp)
  let e₂ := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  constructor
  · intro hx
    have hcoeffPow (n : ℕ) : (x.coeff n) ^ q = x.coeff n := by
      rw [← WittVector.coeff_frobenius_charP]
      exact congrArg (fun y : WittVector q (AlgebraicClosure (ZMod q)) => y.coeff n) hx
    have hcoeffInt (n : ℕ) : ∃ a : ℤ, (a : AlgebraicClosure (ZMod q)) = x.coeff n := by
      apply (mem_bot_iff_intCast q (AlgebraicClosure (ZMod q))).1
      exact (Subfield.mem_bot_iff_pow_eq_self (AlgebraicClosure (ZMod q)) q).2 (hcoeffPow n)
    let c : ℕ → ℤ := fun n => (hcoeffInt n).choose
    let y : WittVector q (ZMod q) := WittVector.mk q (fun n => (c n : ZMod q))
    refine ⟨(e₁.trans e₂).symm (WittVector.equiv q y), ?_⟩
    change WittVector.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))
      ((WittVector.equiv q).symm ((e₁.trans e₂) ((e₁.trans e₂).symm (WittVector.equiv q y)))) = x
    rw [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
    apply WittVector.ext
    intro n
    rw [WittVector.map_coeff]
    change algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (c n : ZMod q) = x.coeff n
    rw [map_intCast]
    exact (hcoeffInt n).choose_spec
  · rintro ⟨z, rfl⟩
    exact rationalPrimeIntegerWittMap_frobenius p hp z

end
end Dubon2026
