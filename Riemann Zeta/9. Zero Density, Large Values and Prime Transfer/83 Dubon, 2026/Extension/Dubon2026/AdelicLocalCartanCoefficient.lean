import Dubon2026.FinitePlaceGL2Cartan
import Dubon2026.UnitaryDoubleCosetCoefficient
import Dubon2026.AdelicLocalCentralCharacter

/-! # Every original local spherical matrix coefficient reduces to a power of the actual Hecke diagonal -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- Actual local Cartan factorization and the proved original central character reduce every genuine local matrix coefficient of original fixed vectors to a nonnegative power of the original Hecke diagonal. -/
theorem adelicCyclicLocal_matrixCoefficient_cartan {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (x y : AdelicCyclicHilbert f)
    (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)),
      adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val x = x)
    (hy : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)),
      adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val y = y)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    ∃ n : ℕ, inner ℂ x (adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g y) =
      inner ℂ x (adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime))
        ((GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
          (finiteAdelicHeckeDiagonal p)) ^ n) y) := by
  obtain ⟨u, n, l, r, hg⟩ := finitePlaceGL2_cartan p (Fact.out : p.Prime) g
  have hl : l.val⁻¹ ∈ finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)) := by
    rw [finitePlaceGL2Gamma0_good_eq_one N p (Fact.out : p.Prime) hpN]
    exact (finitePlaceGL2Gamma0 1 _).inv_mem l.property
  have hr : r.val ∈ finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)) := by
    rw [finitePlaceGL2Gamma0_good_eq_one N p (Fact.out : p.Prime) hpN]
    exact r.property
  refine ⟨n, ?_⟩
  rw [hg]
  exact @unitary_scalar_double_coset_coefficient
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation f _) (adelicCyclicLocalRepresentation_inner f _)
    _ _ _ _ (adelicCyclicLocal_scalar_action f _ u) x y (hx ⟨l.val⁻¹, hl⟩) (hy ⟨r.val, hr⟩)

end
end Dubon2026
