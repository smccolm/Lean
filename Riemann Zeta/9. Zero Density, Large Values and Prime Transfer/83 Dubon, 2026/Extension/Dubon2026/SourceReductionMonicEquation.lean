import Dubon2026.SourceReductionMinimalPolynomial
import Dubon2026.SourceReductionMinimalPolynomialDegree

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> genus
comparison -> preservation of pole bounds. Integral functions on the two
coordinate charts satisfy a literal monic equation over the constant valuation
ring whose coefficient degrees obey the required pole bound. Native polynomial
lifts preserve monicity and degree, replacing the external manual support sums.
Chart integrality and the degree-preserving coordinate remain explicit here;
the actual modular pole-space consumer must supply them. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Polynomial
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem exists_monic_equation_of_integral_charts (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (f : R.integers) (m : ℕ)
    (hint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (f : F))
    (hinv : IsIntegral (Algebra.adjoin L ({(x : F)⁻¹} : Set F))
      ((f : F) * ((x : F) ^ m)⁻¹)) :
    ∃ p : Polynomial (Polynomial A), p.Monic ∧
      (∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m) ∧
      p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F)) (f : F) = 0 := by
  have hxL := transcendental_of_residue_transcendental R x hx
  have hx0 : (x : F) ≠ 0 := fun h => hxL (h ▸ isAlgebraic_zero)
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
  have hcdeg (j : ℕ) : (qL.coeff j).natDegree ≤ (qL.natDegree - j) * m := by
    rw [hqLcoeff]
    rw [show qL.natDegree = q.natDegree from (minpoly.monic hint).natDegree_map _]
    exact natDegree_minpoly_coordinate_coeff_le (x : F) hxL hx0 (f : F) hint m hinv j
      (e.symm (q.coeff j)) (he _)
  have hlift : qL ∈ Polynomial.lifts (Polynomial.mapRingHom A.subtype) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    apply (Polynomial.mem_lifts (qL.coeff j)).mp
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hcA j i⟩, rfl⟩
  obtain ⟨p, hp, hpd, hpm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hqLmonic
  have hcoeff (j : ℕ) : (p.coeff j).map A.subtype = qL.coeff j := by
    simpa only [Polynomial.coeff_map, Polynomial.coe_mapRingHom] using
      congrArg (fun t : Polynomial (Polynomial L) => t.coeff j) hp
  refine ⟨p, hpm, ?_, ?_⟩
  · intro j
    rw [← Polynomial.natDegree_map_eq_of_injective (f := A.subtype) Subtype.val_injective (p.coeff j),
      hcoeff, hpd]
    exact hcdeg j
  · have hcomp : (Polynomial.aeval (x : F)).toRingHom.comp e.symm.toRingHom =
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
