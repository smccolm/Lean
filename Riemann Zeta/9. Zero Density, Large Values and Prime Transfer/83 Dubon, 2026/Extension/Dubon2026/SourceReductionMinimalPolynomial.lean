import Dubon2026.SourceReductionFiniteIntegrality
import Dubon2026.SourceReductionIntegralPolynomials

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> genus
comparison -> preservation of pole bounds. The coefficients of the actual
minimal polynomial over the coordinate polynomial ring are integral in the
prolongation valuation. Finite integral coordinates replace the source's
quantification over valuation extensions. Native polynomial-ring equivalence,
principal ideal transport and fraction-field minimal-polynomial comparison
discharge the remaining algebraic inputs. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem coe_minpoly_adjoin_coeff_mem_integers (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (f : R.integers) (hint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (f : F))
    (j : ℕ) :
    (((minpoly (Algebra.adjoin L ({(x : F)} : Set F)) (f : F)).coeff j :
      Algebra.adjoin L ({(x : F)} : Set F)) : F) ∈ R.integers := by
  have hxL := transcendental_of_residue_transcendental R x hx
  haveI : IsPrincipalIdealRing (Algebra.adjoin L ({(x : F)} : Set F)) :=
    IsPrincipalIdealRing.of_surjective
      (Polynomial.algEquivOfTranscendental L (x : F) hxL).toRingHom
      (Polynomial.algEquivOfTranscendental L (x : F) hxL).surjective
  let S : Subring F :=
    (IntermediateField.adjoin L ({(x : F)} : Set F)).toSubfield.toSubring ⊓ R.integers.toSubring
  have hfintS : IsIntegral S (f : F) := isIntegral_coordinate_intersection R x hx hfin hdeg f
  let W : ValuationSubring (IntermediateField.adjoin L {(x : F)}) :=
    R.integers.comap (IntermediateField.adjoin L {(x : F)}).toSubfield.subtype
  letI : Algebra W F := RingHom.toAlgebra
    ((IntermediateField.adjoin L {(x : F)}).toSubfield.subtype.comp W.subtype)
  letI : IsScalarTower W (IntermediateField.adjoin L {(x : F)}) F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let φ : S →+* W :=
    { toFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hfintW : IsIntegral W (f : F) := by
    refine hfintS.map_of_comp_eq φ (RingHom.id F) ?_
    ext e
    rfl
  have hKcoeff : ∀ i, ((minpoly (IntermediateField.adjoin L {(x : F)}) (f : F)).coeff i : F)
      ∈ R.integers := by
    intro i
    have heq : minpoly (IntermediateField.adjoin L {(x : F)}) (f : F) =
        (minpoly W (f : F)).map (algebraMap W (IntermediateField.adjoin L {(x : F)})) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' _ hfintW
    rw [heq, Polynomial.coeff_map]
    exact ((minpoly W (f : F)).coeff i).2
  have hqK : minpoly (IntermediateField.adjoin L {(x : F)}) (f : F) =
      (minpoly (Algebra.adjoin L ({(x : F)} : Set F)) (f : F)).map
        (algebraMap (Algebra.adjoin L ({(x : F)} : Set F))
          (IntermediateField.adjoin L {(x : F)})) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' _ hint
  have hcoe : (((minpoly (Algebra.adjoin L ({(x : F)} : Set F)) (f : F)).coeff j :
      Algebra.adjoin L ({(x : F)} : Set F)) : F) =
      ((minpoly (IntermediateField.adjoin L {(x : F)}) (f : F)).coeff j : F) := by
    rw [hqK, Polynomial.coeff_map]
    rfl
  rw [hcoe]
  exact hKcoeff j

end
end Dubon2026.SourceCurve.RegularProlongation
