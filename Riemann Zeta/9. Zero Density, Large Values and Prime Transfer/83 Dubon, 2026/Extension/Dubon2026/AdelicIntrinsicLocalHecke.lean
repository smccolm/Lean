import Dubon2026.FinitePlaceHeckeTrace
import Dubon2026.FinitePlaceSphericalLevel
import Dubon2026.AdelicHeckeLocalBridge

/-! # Intrinsic local Hecke trace in the original genuine cusp representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The actual original local Hecke sum is precisely the intrinsic local coset trace with its genuine unitary factor. -/
theorem adelicLocalNormalizedHecke_intrinsic {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N) :
    adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN =
      (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) •
        finitePlaceHeckeTrace N p hpN (adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime))) := rfl

/-- The actual normalized intrinsic local Hecke operator preserves every vector fixed by the genuine original local level group. -/
theorem adelicLocalNormalizedHecke_local_fixed {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert f)
    (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)),
      adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val x = x)
    (g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val
      (adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN x) =
        adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN x := by
  rw [adelicLocalNormalizedHecke_intrinsic]
  simp only [LinearMap.smul_apply, map_smul]
  rw [finitePlaceHeckeTrace_level_fixed N p hpN _ x hx g]

end
end Dubon2026
