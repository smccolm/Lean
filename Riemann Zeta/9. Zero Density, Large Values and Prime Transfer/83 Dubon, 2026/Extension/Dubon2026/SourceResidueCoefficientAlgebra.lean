import Dubon2026.SourceResidueAllLevelDegree
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! DUB-17/18 -> original Frobenius/inertia -> actual good/place reduction
-> coefficient specialization of the modular divisor field. Finite polynomial
relations are scaled so one coefficient is a unit and then reduced literally.
The all-level degree consumer will supply independence of powers of j_N,
so an integral Laurent member specializes into the residue modular field.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, coefficient specialization proof.
No specialization or independence premise is hidden in these constructions. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem coefficientMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) := by
  simp only [HahnSeries.C_apply, coeffMap_single]

theorem coefficientMap_aeval_j {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X]) :
    coeffMap f (aeval (jqModC R) p) = aeval (jqModC S) (p.map f) := by
  have h : (algebraMap S (LaurentSeries S)).comp f = (coeffMap f).comp
      (algebraMap R (LaurentSeries R)) := by
    apply RingHom.ext
    intro r
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C,
      HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
    exact (coefficientMap_C f r).symm
  rw [Polynomial.map_aeval_eq_aeval_map h]
  change Polynomial.aeval ((jqModC R).map f) (p.map f) = _
  rw [map_jqModC]

theorem coefficientMap_valuation_subtype_injective {L : Type*} [Field L] (A : ValuationSubring L) :
    Function.Injective (coeffMap A.subtype) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries L => z.coeff n) h
  simpa [coeffMap_coeff] using this

end
end Dubon2026.SourceFunctionField
