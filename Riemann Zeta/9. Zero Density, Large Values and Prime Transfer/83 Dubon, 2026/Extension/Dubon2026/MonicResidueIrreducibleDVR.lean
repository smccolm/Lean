import Dubon2026.MonicResidueIrreducibleLocalAlgebra
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # The actual residue-irreducible integral root algebra is a DVR -/

namespace Dubon2026
noncomputable section

open Polynomial

/-- A monic polynomial irreducible over the original residue field defines an
actual DVR. Its maximal ideal is the extension of the original maximal ideal;
no unramified extension or valuation is supplied as a hypothesis. -/
theorem monic_residue_irreducible_adjoinRoot_dvr
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (f : R[X]) (hf : f.Monic)
    (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    letI : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime
      ((Polynomial.Monic.irreducible_of_irreducible_map
        (IsLocalRing.residue R) f hf hi).prime)
    IsDiscreteValuationRing (AdjoinRoot f) := by
  have hfi : Irreducible f := Polynomial.Monic.irreducible_of_irreducible_map
    (IsLocalRing.residue R) f hf hi
  haveI : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hfi.prime
  haveI : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  haveI : IsLocalRing (AdjoinRoot f) :=
    monic_residue_irreducible_adjoinRoot_local f hf hi
  have hfn : f.natDegree ≠ 0 := by
    intro h
    apply hfi.not_isUnit
    rw [Polynomial.eq_one_of_monic_natDegree_zero hf h]
    exact isUnit_one
  have hfd : f.degree ≠ 0 := by
    intro h
    exact hfn (Polynomial.natDegree_eq_of_degree_eq_some h)
  have hinj : Function.Injective (algebraMap R (AdjoinRoot f)) :=
    AdjoinRoot.of.injective_of_degree_ne_zero hfd
  have hnf : ¬ IsField (AdjoinRoot f) := fun h =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinj h)
  apply ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnf).out 4 0).mp
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot f)) =
      IsLocalRing.maximalIdeal (AdjoinRoot f) :=
    IsLocalRing.eq_maximalIdeal (monic_residue_irreducible_adjoinRoot_maximal f hi)
  rw [← hmax]
  exact (inferInstance : (IsLocalRing.maximalIdeal R).IsPrincipal).map_ringHom
    (algebraMap R (AdjoinRoot f))

end
end Dubon2026
