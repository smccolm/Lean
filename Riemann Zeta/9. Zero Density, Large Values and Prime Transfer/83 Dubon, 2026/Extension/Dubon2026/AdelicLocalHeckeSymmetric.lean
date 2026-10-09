import Dubon2026.FinitePlaceHeckeSymmetric
import Dubon2026.AdelicIntrinsicLocalHecke
import Dubon2026.AdelicLocalCentralCharacter

/-! # Symmetry of the actual normalized local Hecke action in the original cusp Hilbert space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The original p^(-1/2)-normalized local Hecke operator is symmetric on the actual local integral fixed space; its unitarity and trivial central character are derived from the original cusp representation. -/
theorem adelicLocalNormalizedHecke_symmetric {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (x y : AdelicCyclicHilbert f)
    (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)),
      adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val x = x)
    (hy : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)),
      adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime)) g.val y = y) :
    inner ℂ (adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN x) y =
      inner ℂ x (adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN y) := by
  rw [adelicLocalNormalizedHecke_intrinsic]
  apply @real_scaled_linear_symmetric (AdelicCyclicHilbert f) inferInstance inferInstance
  exact @finitePlaceHeckeTrace_symmetric (AdelicCyclicHilbert f) inferInstance inferInstance
    N p inferInstance inferInstance inferInstance hpN _
    (adelicCyclicLocalRepresentation_inner f _) (adelicCyclicLocal_scalar_action f _) x y hx hy

end
end Dubon2026
