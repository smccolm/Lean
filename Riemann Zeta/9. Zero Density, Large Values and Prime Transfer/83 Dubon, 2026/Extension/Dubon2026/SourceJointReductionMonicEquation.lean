import Dubon2026.SourceJointReductionMinimalPolynomial

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

theorem exists_monic_equation_of_joint_integral_chart
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
    ∃ p : Polynomial (Polynomial A), p.Monic ∧
      p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) f) u = 0 := by
  let R₀ := R i
  let x : R₀.integers := ⟨f, hf i⟩
  let v : R₀.integers := ⟨u, hu i⟩
  have hx : Transcendental (ResidueField A) (R₀.residue x) := htr i
  have hxL := transcendental_of_residue_transcendental R₀ x hx
  let q := minpoly (Algebra.adjoin L ({(x : F)} : Set F)) (v : F)
  let e := Polynomial.algEquivOfTranscendental L (x : F) hxL
  have he (a : Algebra.adjoin L ({(x : F)} : Set F)) :
      Polynomial.aeval (x : F) (e.symm a) = (a : F) := by
    have h := congrArg Subtype.val (e.apply_symm_apply a)
    simpa only [e, Polynomial.algEquivOfTranscendental_apply, ← Subalgebra.aeval_coe] using h
  let qL : Polynomial (Polynomial L) := q.map e.symm.toRingHom
  have hqLmonic : qL.Monic := (minpoly.monic hint).map _
  have hqLcoeff (j : ℕ) : qL.coeff j = e.symm (q.coeff j) :=
    Polynomial.coeff_map e.symm.toRingHom j
  have hcA (j k : ℕ) : (qL.coeff j).coeff k ∈ A := by
    apply coeff_mem_of_aeval_mem_integers R₀ x hx _ _ k
    rw [hqLcoeff]
    rw [he]
    exact coe_minpoly_adjoin_coeff_mem_joint_integers A Fb R hR f hf htr heq u hu hint i j
  have hlift : qL ∈ Polynomial.lifts (Polynomial.mapRingHom A.subtype) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    apply (Polynomial.mem_lifts (qL.coeff j)).mp
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hcA j i⟩, rfl⟩
  obtain ⟨p, hp, _, hpm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hqLmonic
  refine ⟨p, hpm, ?_⟩
  have hcomp : (Polynomial.aeval (x : F)).toRingHom.comp e.symm.toRingHom =
      (Algebra.adjoin L ({(x : F)} : Set F)).val.toRingHom := by
    ext a
    exact he a
  have hroot : qL.eval₂ (Polynomial.aeval (x : F)).toRingHom (v : F) = 0 := by
    change (q.map e.symm.toRingHom).eval₂ (Polynomial.aeval (x : F)).toRingHom (v : F) = 0
    rw [Polynomial.eval₂_map, hcomp]
    exact minpoly.aeval _ _
  rw [← hp, Polynomial.eval₂_map] at hroot
  convert hroot using 1
  congr 1
  ext t <;> simp [x]

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
