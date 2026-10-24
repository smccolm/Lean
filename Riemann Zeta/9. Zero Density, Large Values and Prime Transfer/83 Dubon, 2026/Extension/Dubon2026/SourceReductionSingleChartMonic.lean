import Dubon2026.SourceReductionMinimalPolynomial

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> symmetric-power
continuation -> automorphy and residual association -> original weight-two
Frobenius/inertia -> modular good reduction -> place comparison.
Integral chart functions have integral values at an original place centered
over an integral coordinate value; zero Gauss residue forces that value into
the coefficient maximal ideal. These are the properness inputs for the
actual reduction-place construction, not a supplied place-map certificate.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.
The existing local minimal-polynomial integrality theorem replaces the
external valuation-extension and monic-equation development. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Polynomial
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem exists_monic_equation_of_integral_chart (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (f : R.integers)
    (hint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (f : F)) :
    ∃ p : Polynomial (Polynomial A), p.Monic ∧
      p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F)) (f : F) = 0 := by
  have hxL := transcendental_of_residue_transcendental R x hx
  let q := minpoly (Algebra.adjoin L ({(x : F)} : Set F)) (f : F)
  let e := Polynomial.algEquivOfTranscendental L (x : F) hxL
  have he (a : Algebra.adjoin L ({(x : F)} : Set F)) :
      Polynomial.aeval (x : F) (e.symm a) = (a : F) := by
    have h := congrArg Subtype.val (e.apply_symm_apply a)
    simpa only [e, Polynomial.algEquivOfTranscendental_apply, ← Subalgebra.aeval_coe] using h
  let qL : Polynomial (Polynomial L) := q.map e.symm.toRingHom
  have hqLmonic : qL.Monic := (minpoly.monic hint).map _
  have hqLcoeff (j : ℕ) : qL.coeff j = e.symm (q.coeff j) :=
    Polynomial.coeff_map e.symm.toRingHom j
  have hcA (j i : ℕ) : (qL.coeff j).coeff i ∈ A := by
    apply coeff_mem_of_aeval_mem_integers R x hx _ _ i
    rw [hqLcoeff]
    rw [he]
    exact coe_minpoly_adjoin_coeff_mem_integers R x hx hfin hdeg f hint j
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
  have hroot : qL.eval₂ (Polynomial.aeval (x : F)).toRingHom (f : F) = 0 := by
    change (q.map e.symm.toRingHom).eval₂ (Polynomial.aeval (x : F)).toRingHom (f : F) = 0
    rw [Polynomial.eval₂_map, hcomp]
    exact minpoly.aeval _ _
  rw [← hp, Polynomial.eval₂_map] at hroot
  convert hroot using 1
  congr 1
  ext t <;> simp

end
end Dubon2026.SourceCurve.RegularProlongation
