import Dubon2026.SourceIntegralDiamondScalarFixedField
import Dubon2026.SourceIntegralDiamondFixedPlaceTransitivity

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> residue fiber bounds. The proved fixed-field comparison changes equality
over the full modular base into equality over the actual diamond fixed field.
Native Galois transitivity then supplies a literal Gamma0 matrix. The coordinate
degree is the narrower original residue theorem, discharged by the next consumer.
-/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open IntermediateField CongruenceSubgroup GammaOne SourceCurve
open scoped MatrixGroups IntermediateField

theorem diamond_exists_comapEquiv_of_fullBase_comap_eq
    (L : Type*) [Field L] [IsAlgClosed L] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] [Algebra (ZMod ℓ) L] (hℓN : ¬ ℓ ∣ N)
    (hdegree : relfinrank L⟮jqModC L⟯ (qExpFunctionFieldC L (Gamma1 N)) =
      (plusMinus (Gamma1 N)).index)
    (w w' : Place L (qExpFunctionFieldC L (Gamma1 N)))
    (h : w'.toValuationSubring.comap
        (IntermediateField.inclusion (fullBase_le_originalField L N)).toRingHom =
      w.toValuationSubring.comap
        (IntermediateField.inclusion (fullBase_le_originalField L N)).toRingHom) :
    ∃ γ : Gamma0 N, w.comapEquiv (reducedFieldActionOver L N ℓ hℓN γ) = w' := by
  let F := qExpFunctionFieldC L (Gamma1 N)
  let B := modularFunctionFieldCoeff N L
  let X := IntermediateField.fixedField (reducedFieldActionOver L N ℓ hℓN).range
  have hX : lift X = B :=
    scalar_fixedField_eq_fullBase_of_coordinate_degree L N ℓ hℓN hdegree
  apply diamond_exists_comapEquiv_of_restrict_fixed_eq L N ℓ hℓN w w'
  apply Place.ext
  ext u
  rw [Place.mem_restrict_iff, Place.mem_restrict_iff]
  have hu : ((u : F) : LaurentSeries L) ∈ B := by
    rw [← hX]
    exact (mem_lift (u : F)).mpr u.property
  let v : B := ⟨((u : F) : LaurentSeries L), hu⟩
  have hv : IntermediateField.inclusion (fullBase_le_originalField L N) v = (u : F) :=
    Subtype.ext rfl
  have hx := congrArg (fun V : ValuationSubring B => v ∈ V) h
  change (IntermediateField.inclusion (fullBase_le_originalField L N) v ∈
    w'.toValuationSubring) = (IntermediateField.inclusion
      (fullBase_le_originalField L N) v ∈ w.toValuationSubring) at hx
  rw [hv] at hx
  exact Iff.of_eq hx

end
end Dubon2026.SourceFunctionField.IntegralDiamond
