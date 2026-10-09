import Dubon2026.FinitePlaceHeckeCosets
import Dubon2026.RepresentationConjugateFixed
import Dubon2026.RepresentationCosetTrace

/-! # The original single-prime Hecke sum is the genuine intrinsic local coset trace -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The actual local Hecke sum from the genuine intrinsic p+1-coset transversal. -/
def finitePlaceHeckeTrace (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
    (ρ : Representation ℂ
      (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V) :
    Module.End ℂ V :=
  ∑ i : Option (ZMod p), ρ
    (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
        (finiteAdelicHeckeDiagonal p)⁻¹))

/-- The intrinsic local conjugation stabilizer fixes the actual inverse-diagonal translate of each original local level-fixed vector. -/
theorem finitePlaceHecke_diagonal_fixed (N p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ
      (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (x : V) (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val x = x)
    (h : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)))
    (hh : h ∈ finitePlaceHeckeUpper N p (Fact.out : p.Prime)) :
    ρ h.val (ρ (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      (finiteAdelicHeckeDiagonal p))⁻¹ x) =
    ρ (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      (finiteAdelicHeckeDiagonal p))⁻¹ x :=
  representation_conjugate_fixed ρ _ _ x hx h.val hh

/-- The genuine intrinsic local Hecke trace preserves the full original local level-fixed space. -/
theorem finitePlaceHeckeTrace_level_fixed (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N)
    (ρ : Representation ℂ
      (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (x : V) (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val x = x)
    (g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime))) :
    ρ g.val (finitePlaceHeckeTrace N p hpN ρ x) = finitePlaceHeckeTrace N p hpN ρ x := by
  let K := finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime))
  let d := GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
    (finiteAdelicHeckeDiagonal p)
  have h := representation_coset_trace_invariant (ρ.comp K.subtype)
    (finitePlaceHeckeUpper N p (Fact.out : p.Prime)) (ρ d⁻¹ x)
    (finitePlaceHecke_diagonal_fixed N p ρ x hx)
    (fun i => finiteAdelicLevelAt N (rationalPrimePlace p (Fact.out : p.Prime))
      (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i))⁻¹)
    (finitePlaceHeckeCosetEquiv N p hpN) (finitePlaceHeckeCosetEquiv_apply N p hpN) g
  change ρ g.val (∑ i : Option (ZMod p),
    ρ (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹) (ρ d⁻¹ x)) =
    ∑ i : Option (ZMod p),
      ρ (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
        (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹) (ρ d⁻¹ x) at h
  simp_rw [← Module.End.mul_apply, ← map_mul] at h
  simpa only [finitePlaceHeckeTrace, LinearMap.sum_apply, map_mul, map_inv, d] using h

end
end Dubon2026
