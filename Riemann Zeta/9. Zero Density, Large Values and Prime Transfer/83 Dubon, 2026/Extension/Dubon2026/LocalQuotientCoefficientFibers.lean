import Dubon2026.OriginalCoefficientFramedEquivalence
import Dubon2026.LocalAdicQuotientResidue

/-! # Genuine residue-preserving coefficient maps through a local quotient -/

namespace Dubon2026

noncomputable section

variable {O R A : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]

/-- The original residue-field identification transported through the actual local coefficient quotient. -/
def originalLocalQuotientResidueEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (J : Ideal R) [IsLocalRing (R ⧸ J)] :
    IsLocalRing.ResidueField (R ⧸ J) ≃ₐ[O] IsLocalRing.ResidueField O :=
  (localQuotientResidueAlgEquiv (O := O) J).symm.trans eR

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The actual local quotient preserves the original coefficient reduction. -/
theorem originalLocalQuotientResidueEquiv_original
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (J : Ideal R) [IsLocalRing (R ⧸ J)] (r : R) :
    localCoefficientReduction (originalLocalQuotientResidueEquiv eR J)
      (Ideal.Quotient.mk J r) = localCoefficientReduction eR r := by
  change eR ((localQuotientResidueAlgEquiv (O := O) J).symm
    (IsLocalRing.residue (R ⧸ J) (Ideal.Quotient.mk J r))) = eR (IsLocalRing.residue R r)
  rw [← localQuotientResidueAlgEquiv_residue (O := O) J r, AlgEquiv.symm_apply_apply]

/-- Restrict a genuine continuous residue-preserving coefficient map to the original coefficient ring. -/
def originalQuotientCoefficientRestriction
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (J : Ideal R) [IsLocalRing (R ⧸ J)]
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR J) eA) :
    {g : OriginalContinuousCoefficientFiber eR eA // J ≤ RingHom.ker g.val.toRingHom} := by
  refine ⟨⟨f.val.comp (Ideal.Quotient.mkₐ O J),
    f.property.1.comp (QuotientRing.isOpenQuotientMap_mk J).continuous, ?_⟩, ?_⟩
  · apply AlgHom.ext
    intro r
    exact (DFunLike.congr_fun f.property.2 (Ideal.Quotient.mk J r)).trans
      (originalLocalQuotientResidueEquiv_original eR J r)
  · intro r hr
    change f.val (Ideal.Quotient.mk J r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- Factor an actual continuous residue-preserving coefficient map through the original ideal it kills. -/
def originalQuotientCoefficientFactor
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (J : Ideal R) [IsLocalRing (R ⧸ J)]
    (g : {f : OriginalContinuousCoefficientFiber eR eA // J ≤ RingHom.ker f.val.toRingHom}) :
    OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR J) eA := by
  let f := Ideal.Quotient.liftₐ J g.val.val (fun _ hr => g.property hr)
  refine ⟨f, ?_, ?_⟩
  · apply (QuotientRing.isOpenQuotientMap_mk J).isQuotientMap.continuous_iff.mpr
    exact g.val.property.1
  · apply AlgHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (DFunLike.congr_fun g.val.property.2 r).trans
      (originalLocalQuotientResidueEquiv_original eR J r).symm

/-- Genuine continuous residue-preserving coefficient maps from the actual local quotient are precisely the original such maps killing its actual ideal. -/
def originalLocalQuotientCoefficientFiberEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (J : Ideal R) [IsLocalRing (R ⧸ J)] :
    OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR J) eA ≃
      {f : OriginalContinuousCoefficientFiber eR eA // J ≤ RingHom.ker f.val.toRingHom} where
  toFun := originalQuotientCoefficientRestriction eR eA J
  invFun := originalQuotientCoefficientFactor eR eA J
  left_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply AlgHom.ext
    intro r
    rfl

/-- The original restriction map is bijective between all actual quotient coefficient maps and all original coefficient maps killing the ideal. -/
theorem originalLocalQuotientCoefficientFiberEquiv_bijective
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (J : Ideal R) [IsLocalRing (R ⧸ J)] :
    Function.Bijective (originalLocalQuotientCoefficientFiberEquiv eR eA J) :=
  (originalLocalQuotientCoefficientFiberEquiv eR eA J).bijective

/-- The genuine quotient coefficient equivalence retains every original coefficient value. -/
theorem originalLocalQuotientCoefficientFiberEquiv_evaluation
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (J : Ideal R) [IsLocalRing (R ⧸ J)]
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR J) eA)
    (r : R) :
    (originalLocalQuotientCoefficientFiberEquiv eR eA J f).val.val r =
      f.val (Ideal.Quotient.mk J r) := rfl

end
end Dubon2026
