import Dubon2026.RelativeDualNumberResidue
import Dubon2026.DualNumberCoordinateKernel

/-! # Original relative residue derivations and genuine residual dual-number coefficient lifts -/

namespace Dubon2026

noncomputable section

variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- The actual constant dual-number lift of the original true coefficient residue map. -/
def originalResidueConstantDualLift
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    R →ₐ[O] DualNumber (IsLocalRing.ResidueField O) :=
  (TrivSqZeroExt.inlAlgHom O (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O)).comp
    (localCoefficientReduction eR)

/-- All original algebraic dual-number coefficient lifts of the genuine original residue map. -/
def OriginalRelativeDualNumberFiber
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :=
  {f : R →ₐ[O] DualNumber (IsLocalRing.ResidueField O) //
    (TrivSqZeroExt.fstHom O (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O)).comp f =
      localCoefficientReduction eR}

/-- Actual derivations relative to the original coefficient ring, with the coefficient action fixed by its actual original constant residue point. -/
abbrev OriginalResidueDerivations
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :=
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  Derivation O R (TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O))

omit [IsLocalRing R] in
/-- Over the original coefficient base, equality modulo the genuine dual-number epsilon ideal is exactly equality of first-coordinate maps. -/
theorem relativeDualNumberQuotient_comp_eq_iff
    (f g : R →ₐ[O] DualNumber (IsLocalRing.ResidueField O)) :
    (Ideal.Quotient.mkₐ O (TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O)
      (IsLocalRing.ResidueField O))).comp f =
        (Ideal.Quotient.mkₐ O (TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O)
          (IsLocalRing.ResidueField O))).comp g ↔
      (TrivSqZeroExt.fstHom O (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O)).comp f =
        (TrivSqZeroExt.fstHom O (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O)).comp g := by
  rw [AlgHom.ext_iff, AlgHom.ext_iff]
  apply forall_congr'
  intro x
  change Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O)
    (IsLocalRing.ResidueField O)) (f x) =
      Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal (IsLocalRing.ResidueField O)
        (IsLocalRing.ResidueField O)) (g x) ↔ (f x).fst = (g x).fst
  rw [Ideal.Quotient.eq]
  change (TrivSqZeroExt.fstHom O (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O))
    (f x - g x) = 0 ↔ _
  rw [map_sub, sub_eq_zero]
  rfl

/-- The actual square-zero lifting theorem identifies the genuine original relative residue derivations with all original dual-number lifts of the same residue point. -/
def originalResidueDerivationEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    OriginalResidueDerivations eR ≃ OriginalRelativeDualNumberFiber eR := by
  let K := IsLocalRing.ResidueField O
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  letI : IsScalarTower O R (DualNumber K) := IsScalarTower.of_algHom (originalResidueConstantDualLift eR)
  have hc : IsScalarTower.toAlgHom O R (DualNumber K ⧸ TrivSqZeroExt.kerIdeal K K) =
      (Ideal.Quotient.mkₐ O (TrivSqZeroExt.kerIdeal K K)).comp (originalResidueConstantDualLift eR) := by
    ext x
    rfl
  have hf (f : R →ₐ[O] DualNumber K) :
      (Ideal.Quotient.mkₐ O (TrivSqZeroExt.kerIdeal K K)).comp f =
        IsScalarTower.toAlgHom O R (DualNumber K ⧸ TrivSqZeroExt.kerIdeal K K) ↔
          (TrivSqZeroExt.fstHom O K K).comp f = localCoefficientReduction eR := by
    rw [hc, relativeDualNumberQuotient_comp_eq_iff]
    rfl
  exact (derivationToSquareZeroEquivLift (R := O) (A := R)
    (TrivSqZeroExt.kerIdeal K K) (TrivSqZeroExt.kerIdeal_sq K K)).trans
      { toFun := fun f => ⟨f.val, (hf f.val).mp f.property⟩
        invFun := fun f => ⟨f.val, (hf f.val).mpr f.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

/-- The genuine original relative derivation gives its actual epsilon correction of the same constant residue point. -/
theorem originalResidueDerivationEquiv_apply
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (d : OriginalResidueDerivations eR) (r : R) :
    (originalResidueDerivationEquiv eR d).val r =
      (d r : DualNumber (IsLocalRing.ResidueField O)) + originalResidueConstantDualLift eR r := rfl

end
end Dubon2026
