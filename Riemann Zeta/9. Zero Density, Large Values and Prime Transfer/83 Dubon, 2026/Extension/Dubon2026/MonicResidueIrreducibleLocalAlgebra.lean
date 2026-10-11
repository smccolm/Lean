import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # The actual integral root algebra has a unique maximal ideal -/

namespace Dubon2026
noncomputable section

open Polynomial

/-- Reduction of the original root algebra is the actual root field of the
irreducible residue polynomial, so the extended maximal ideal is maximal. -/
theorem monic_residue_irreducible_adjoinRoot_maximal
    {R : Type} [CommRing R] [IsLocalRing R] (f : R[X])
    (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    ((IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot f))).IsMaximal := by
  haveI : Fact (Irreducible (f.map (IsLocalRing.residue R))) := ⟨hi⟩
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot f))
  let e : (AdjoinRoot f ⧸ J) ≃+* AdjoinRoot (f.map (IsLocalRing.residue R)) :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (IsLocalRing.maximalIdeal R) f
  have h := RingHom.ker_isMaximal_of_surjective
    (e.toRingHom.comp (Ideal.Quotient.mk J))
    (e.surjective.comp Ideal.Quotient.mk_surjective)
  rwa [RingHom.ker_comp_of_injective _ e.injective, Ideal.mk_ker] at h

/-- The genuine finite integral root algebra is local: every maximal ideal
contracts to the original maximal ideal and hence equals its proved maximal extension. -/
theorem monic_residue_irreducible_adjoinRoot_local
    {R : Type} [CommRing R] [IsLocalRing R] (f : R[X]) (hf : f.Monic)
    (hi : Irreducible (f.map (IsLocalRing.residue R))) :
    IsLocalRing (AdjoinRoot f) := by
  haveI : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot f))
  have hJ : J.IsMaximal := monic_residue_irreducible_adjoinRoot_maximal f hi
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨J, hJ, ?_⟩
  intro Q hQ
  haveI : Q.IsMaximal := hQ
  have hc : Q.comap (algebraMap R (AdjoinRoot f)) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) Q)
  have hle : J ≤ Q := Ideal.map_le_iff_le_comap.mpr hc.ge
  exact (hJ.eq_of_le hQ.ne_top hle).symm

end
end Dubon2026
