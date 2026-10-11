import Dubon2026.MonicResidueIrreducibleLocalAlgebra
import Mathlib.FieldTheory.Finiteness

/-! # The genuine residue field of the original integral root algebra -/

namespace Dubon2026
noncomputable section

open Polynomial

/-- The actual residue field of the integral root algebra is identified
with the original residue root field. Both quotients use the original ideals. -/
def monicRootResidueEquiv
    {R : Type} [CommRing R] [IsLocalRing R] (f : R[X]) (hf : f.Monic)
    (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    letI : IsLocalRing (AdjoinRoot f) := monic_residue_irreducible_adjoinRoot_local f hf hi
    IsLocalRing.ResidueField (AdjoinRoot f) ≃+*
      AdjoinRoot (f.map (IsLocalRing.residue R)) := by
  haveI : IsLocalRing (AdjoinRoot f) := monic_residue_irreducible_adjoinRoot_local f hf hi
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot f)) =
      IsLocalRing.maximalIdeal (AdjoinRoot f) :=
    IsLocalRing.eq_maximalIdeal (monic_residue_irreducible_adjoinRoot_maximal f hi)
  exact (Ideal.quotEquivOfEq hmax.symm).trans
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (IsLocalRing.maximalIdeal R) f)

/-- The actual residue degree is the degree of the original monic polynomial,
and hence its residue cardinality is the corresponding power of the original
finite residue cardinality. -/
theorem monicRootResidue_natCard
    {R : Type} [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    (f : R[X]) (hf : f.Monic) (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    letI : IsLocalRing (AdjoinRoot f) := monic_residue_irreducible_adjoinRoot_local f hf hi
    Nat.card (IsLocalRing.ResidueField (AdjoinRoot f)) =
      Nat.card (IsLocalRing.ResidueField R) ^ f.natDegree := by
  haveI : IsLocalRing (AdjoinRoot f) := monic_residue_irreducible_adjoinRoot_local f hf hi
  haveI : Fact (Irreducible (f.map (IsLocalRing.residue R))) := ⟨hi⟩
  haveI : Module.Finite (IsLocalRing.ResidueField R)
      (AdjoinRoot (f.map (IsLocalRing.residue R))) :=
    (hf.map (IsLocalRing.residue R)).finite_adjoinRoot
  rw [Nat.card_congr (monicRootResidueEquiv f hf hi).toEquiv,
    Module.natCard_eq_pow_finrank (K := IsLocalRing.ResidueField R)]
  congr 1
  exact (AdjoinRoot.powerBasis' (hf.map (IsLocalRing.residue R))).finrank.trans
    (hf.natDegree_map (IsLocalRing.residue R))

end
end Dubon2026
