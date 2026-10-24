import Dubon2026.SourceJointReductionMonicEquation
import Dubon2026.SourceReductionEquationSpecialization

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

theorem isIntegral_residue_of_joint_integral_chart
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
    (hint : IsIntegral (Algebra.adjoin L ({f} : Set F)) u) (i : ι) :
    IsIntegral (Algebra.adjoin (ResidueField A) {(R i).residue ⟨f, hf i⟩})
      ((R i).residue ⟨u, hu i⟩) := by
  let R₀ := R i
  let x : R₀.integers := ⟨f, hf i⟩
  let v : R₀.integers := ⟨u, hu i⟩
  obtain ⟨p, hp, hroot⟩ := exists_monic_equation_of_joint_integral_chart A Fb R hR f hf htr heq u hu hint i
  let B := Algebra.adjoin (ResidueField A) ({R₀.residue x} : Set (Fb i))
  let y : B := ⟨R₀.residue x, Algebra.self_mem_adjoin_singleton _ _⟩
  let φ : Polynomial A →+* B := Polynomial.eval₂RingHom
    ((algebraMap (ResidueField A) B).comp (IsLocalRing.residue A)) y
  refine ⟨p.map φ, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap B (Fb i)).comp φ =
      Polynomial.eval₂RingHom (resConst A (Fb i)) (R₀.residue x) := by
    ext a <;> simp [φ, y, resConst]
  rw [hcomp]
  exact eval₂_residue_eq_zero R₀ x v p hroot

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
