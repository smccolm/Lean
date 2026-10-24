import Dubon2026.SourceJointReductionFiniteIntegrality
import Dubon2026.SourceReductionIntegralPolynomials

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality -> integrality of simultaneous residue charts.
The already proved finite-coordinate and monic-polynomial route is extended
to the joint integral ring. It replaces the external valuation-extension
classification. All degree and finite-coordinate inputs remain explicit
until the actual modular Kummer consumer derives them. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

theorem coe_minpoly_adjoin_coeff_mem_joint_integers
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [∀ i, FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) =
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (u : F) (hu : ∀ i, u ∈ (R i).integers)
    (hint : IsIntegral (Algebra.adjoin L ({f} : Set F)) u) (i : ι) (j : ℕ) :
    (((minpoly (Algebra.adjoin L ({f} : Set F)) u).coeff j :
      Algebra.adjoin L ({f} : Set F)) : F) ∈ (R i).integers := by
  let R₀ := R i
  let x : R₀.integers := ⟨f, hf i⟩
  let v : R₀.integers := ⟨u, hu i⟩
  have hx : Transcendental (ResidueField A) (R₀.residue x) := htr i
  have hxL := transcendental_of_residue_transcendental R₀ x hx
  haveI : IsPrincipalIdealRing (Algebra.adjoin L ({(x : F)} : Set F)) :=
    IsPrincipalIdealRing.of_surjective
      (Polynomial.algEquivOfTranscendental L (x : F) hxL).toRingHom
      (Polynomial.algEquivOfTranscendental L (x : F) hxL).surjective
  let S : Subring F :=
    (IntermediateField.adjoin L ({(x : F)} : Set F)).toSubfield.toSubring ⊓ ⨅ l, (R l).integers.toSubring
  have hfintS : IsIntegral S (v : F) := isIntegral_joint_coordinate_intersection A Fb R hR f hf htr heq u hu
  let W : ValuationSubring (IntermediateField.adjoin L {(x : F)}) :=
    R₀.integers.comap (IntermediateField.adjoin L {(x : F)}).toSubfield.subtype
  letI : Algebra W F := RingHom.toAlgebra
    ((IntermediateField.adjoin L {(x : F)}).toSubfield.subtype.comp W.subtype)
  letI : IsScalarTower W (IntermediateField.adjoin L {(x : F)}) F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let φ : S →+* W :=
    { toFun := fun e => ⟨⟨e.1, e.2.1⟩, Subring.mem_iInf.mp e.2.2 i⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hfintW : IsIntegral W (v : F) := by
    refine hfintS.map_of_comp_eq φ (RingHom.id F) ?_
    ext e
    rfl
  have hKcoeff : ∀ i, ((minpoly (IntermediateField.adjoin L {(x : F)}) (v : F)).coeff i : F)
      ∈ R₀.integers := by
    intro i
    have heq : minpoly (IntermediateField.adjoin L {(x : F)}) (v : F) =
        (minpoly W (v : F)).map (algebraMap W (IntermediateField.adjoin L {(x : F)})) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' _ hfintW
    rw [heq, Polynomial.coeff_map]
    exact ((minpoly W (v : F)).coeff i).2
  have hqK : minpoly (IntermediateField.adjoin L {(x : F)}) (v : F) =
      (minpoly (Algebra.adjoin L ({(x : F)} : Set F)) (v : F)).map
        (algebraMap (Algebra.adjoin L ({(x : F)} : Set F))
          (IntermediateField.adjoin L {(x : F)})) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' _ hint
  have hcoe : (((minpoly (Algebra.adjoin L ({(x : F)} : Set F)) (v : F)).coeff j :
      Algebra.adjoin L ({(x : F)} : Set F)) : F) =
      ((minpoly (IntermediateField.adjoin L {(x : F)}) (v : F)).coeff j : F) := by
    rw [hqK, Polynomial.coeff_map]
    rfl
  rw [hcoe]
  exact hKcoeff j

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
