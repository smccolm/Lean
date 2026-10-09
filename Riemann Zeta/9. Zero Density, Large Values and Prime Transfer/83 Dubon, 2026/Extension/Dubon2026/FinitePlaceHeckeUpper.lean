import Dubon2026.FiniteAdelicLevelLocalization
import Dubon2026.FiniteAdelicHeckeLocalSupport

/-! # Intrinsic local Hecke stabilizer and its original full adelic preimage -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original full adelic upper Hecke subgroup is exactly the actual conjugation stabilizer of the original level group. -/
theorem finiteAdelicHeckeUpper_iff_conjugate (N p : ℕ) [NeZero p] [Fact p.Prime]
    (g : finiteAdeleGL2Gamma0 N) :
    g ∈ finiteAdelicHeckeUpper N p ↔
      finiteAdelicHeckeDiagonal p * g.val * (finiteAdelicHeckeDiagonal p)⁻¹ ∈ finiteAdeleGL2Gamma0 N := by
  constructor
  · exact finiteAdelicHeckeUpper_conjugate_mem N p g
  · intro h
    apply (finiteAdelicHeckeUpper_mem_iff N p g).mpr
    apply (finiteAdeleLevelMultiple_iff p _).mpr
    have he := h.1.1 0 1
    rw [finiteAdelicHeckeDiagonal_conjugate_val] at he
    exact he

/-- The genuine local subgroup of integral level matrices that remain at that level after conjugation by the actual p-Hecke diagonal. -/
def finitePlaceHeckeUpper (N p : ℕ) [NeZero p] (hp : p.Prime) :
    Subgroup (finitePlaceGL2Gamma0 N (rationalPrimePlace p hp)) :=
  (finitePlaceGL2Gamma0 N (rationalPrimePlace p hp)).comap
    ((MulAut.conj (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
      (finiteAdelicHeckeDiagonal p))).toMonoidHom.comp
        (finitePlaceGL2Gamma0 N (rationalPrimePlace p hp)).subtype)

/-- Original full adelic Hecke membership is precisely the genuine intrinsic local conjugation condition at its prime. -/
theorem finiteAdelicHeckeUpper_local_iff (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (g : finiteAdeleGL2Gamma0 N) :
    g ∈ finiteAdelicHeckeUpper N p ↔
      finiteAdelicLevelAt N (rationalPrimePlace p (Fact.out : p.Prime)) g ∈
        finitePlaceHeckeUpper N p (Fact.out : p.Prime) := by
  rw [finiteAdelicHeckeUpper_iff_conjugate]
  change _ ↔ GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
    (finiteAdelicHeckeDiagonal p) *
    GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime))) g.val *
    (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      (finiteAdelicHeckeDiagonal p))⁻¹ ∈ finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime))
  constructor
  · intro h
    have hh := (finiteAdeleGL2Gamma0_iff_places N _).mp h (rationalPrimePlace p (Fact.out : p.Prime))
    simpa only [map_mul, map_inv] using hh
  · intro h
    apply (finiteAdeleGL2Gamma0_iff_places N _).mpr
    intro w
    rw [map_mul, map_mul, map_inv]
    by_cases hw : w = rationalPrimePlace p (Fact.out : p.Prime)
    · subst w
      exact h
    · have hd := finiteAdelicHeckeDiagonal_local_level N p (Fact.out : p.Prime) w hw
      have hg := (finiteAdeleGL2Gamma0_iff_places N g.val).mp g.property w
      exact (finitePlaceGL2Gamma0 N w).mul_mem ((finitePlaceGL2Gamma0 N w).mul_mem hd hg)
        ((finitePlaceGL2Gamma0 N w).inv_mem hd)

end
end Dubon2026
