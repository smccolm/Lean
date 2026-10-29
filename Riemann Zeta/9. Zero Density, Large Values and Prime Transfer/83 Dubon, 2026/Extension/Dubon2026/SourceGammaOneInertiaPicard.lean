import Dubon2026.SourceGammaOneInertiaPlaceReduction
import Dubon2026.SourceGammaOneHeckeArithmetic

/-! DUB-17/18 -> original Gamma1 Tate inertia -> original Picard torsion.
The literal divisor pushforward carries place invariance to the actual
Picard quotient. Injectivity of the constructed specialization on invertible
torsion then proves inertia triviality on the original arithmetic action.
Only coordinate-degree and genus preservation remain geometric inputs. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve IntermediateField
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M : ℕ) [NeZero M]
local notation "Δ" => CongruenceSubgroup.Gamma1 M
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => functionFieldOver Δ Qbar
local notation "Fb" => residueImage A Δ

omit [NeZero M] in
theorem reduction_arithmeticDivisor_invariant
    (R : ConstantReduction A FF Fb) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hplace : ∀ P : Place Qbar FF, R.placeMap (arithmeticPlace Δ τ P) = R.placeMap P)
    (D : Divisor Qbar FF) :
    R.divMap (arithmeticDivisorEquiv Δ τ D) = R.divMap D := by
  induction D using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add P n D _ _ ih =>
    rw [map_add, map_add, map_add, ih]
    congr 1
    change Finsupp.mapDomain R.placeMap
        (Finsupp.equivMapDomain (arithmeticPlaceEquiv Δ τ) (Finsupp.single P n)) =
      Finsupp.mapDomain R.placeMap (Finsupp.single P n)
    rw [Finsupp.equivMapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    exact congrArg (fun Q => Finsupp.single Q n) (hplace P)

theorem reduction_arithmeticPicard_invariant
    (R : ConstantReduction A FF Fb) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hplace : ∀ P : Place Qbar FF, R.placeMap (arithmeticPlace Δ τ P) = R.placeMap P)
    (x : Pic0 Qbar FF) :
    R.pic0Map (gamma1ArithmeticPicardRep Qbar M τ x) = R.pic0Map x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  have hT : ModularGroup.T ∈ Δ := by simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T]
  change R.pic0Map (Pic0.mk (arithmeticDegZero Δ hT τ D)) = R.pic0Map (Pic0.mk D)
  rw [ConstantReduction.pic0Map_mk, ConstantReduction.pic0Map_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact reduction_arithmeticDivisor_invariant A M R τ hplace D.val

theorem gammaOne_arithmeticPicard_eq_self_of_inertia_of_degree_genus_eq
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Δ Qbar⟯ FF =
      Module.finrank kk⟮residueJCoordinate A Δ⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar FF)
    (m : ℕ) (hm : (m : kk) ≠ 0) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype)
    (x : Pic0 Qbar FF) (hx : x ∈ Pic0.torsion m) :
    gamma1ArithmeticPicardRep Qbar M τ x = x := by
  obtain ⟨R, _, hinj, hplace⟩ :=
    exists_gammaOne_reduction_invariant_on_inertia_of_degree_genus_eq A M hdeg hgen
  apply hinj m hm (gamma1ArithmeticPicardRep_torsion M τ m x hx) hx
  exact reduction_arithmeticPicard_invariant A M R τ (hplace τ hτ) x

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
