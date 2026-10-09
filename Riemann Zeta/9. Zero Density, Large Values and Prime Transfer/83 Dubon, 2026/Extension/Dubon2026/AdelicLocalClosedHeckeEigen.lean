import Dubon2026.AdelicLocalClosedUnitReference
import Dubon2026.FinitePlaceHeckeLevelIndependence

/-! # The intrinsic level-one Hecke eigenvalue of the original local unit vector -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)

include hpN

omit [NeZero p] in
/-- At each good prime, the original ambient unit reference is fixed by the actual full local integral group. -/
theorem adelicCyclicUnitReference_good_fixed
    (g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g.val
      (adelicCyclicUnitReference F.toCuspForm) = adelicCyclicUnitReference F.toCuspForm := by
  have hK := finitePlaceGL2Gamma0_good_eq_one N p (Fact.out : p.Prime) hpN
  have hg := adelicCyclicHilbertGenerator_mem_localFixed F.toCuspForm
    (rationalPrimePlace p (Fact.out : p.Prime)) ⟨g.val, hK.symm ▸ g.property⟩
  unfold adelicCyclicUnitReference
  rw [map_smul]
  exact congrArg (fun x : AdelicCyclicHilbert F.toCuspForm =>
    (‖adelicCyclicHilbertGenerator F.toCuspForm‖ : ℂ)⁻¹ • x) hg

omit [NeZero p] in
/-- The actual closed local unit vector retains its full integral-fixed equation. -/
theorem adelicLocalClosedUnitReference_good_fixed
    (g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g.val
      (adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
        adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) :=
  Subtype.ext (adelicCyclicUnitReference_good_fixed F hpN g)

/-- The genuine intrinsic level-one coset trace acts on the original closed local unit vector by the original normalized Fourier coefficient times the required square root. -/
theorem adelicLocalClosedUnitReference_hecke_eigen :
    finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p)
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
    ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) •
      adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) := by
  apply Subtype.ext
  have ht := finitePlaceHeckeTrace_intertwines 1 p (Nat.coprime_one_right p)
    (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).subtype
    (fun _ _ => rfl)
    (adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
  have he := @finitePlaceHeckeTrace_good_eq_one (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance N p inferInstance inferInstance inferInstance hpN
    (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (adelicCyclicLocalRepresentation_inner F.toCuspForm _)
    (adelicCyclicLocal_scalar_action F.toCuspForm _) (adelicCyclicUnitReference F.toCuspForm)
    (adelicCyclicUnitReference_good_fixed F hpN)
  have hs : finitePlaceHeckeTrace N p hpN
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicCyclicUnitReference F.toCuspForm) =
        ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) • adelicCyclicUnitReference F.toCuspForm := by
    unfold adelicCyclicUnitReference
    rw [map_smul, adelicLocalHeckeTrace_primitive_generator, smul_comm]
  exact ht.trans (he.symm.trans hs)

end
end Dubon2026
