import Mathlib.RingTheory.Valuation.LocalSubring

/-! DUB-17/18 -> arithmetic torsion comparison -> principal-divisor descent
-> trace coefficients regular at new constant-field places. The native integral
closure intersection theorem supplies the valuation criterion needed to prove
trace integrality, replacing the external direct polynomial construction.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section

theorem isIntegral_of_forall_mem_valuationSubring {R L : Type*} [CommRing R] [Field L]
    [Algebra R L] (w : L)
    (h : ∀ B : ValuationSubring L, (∀ r : R, algebraMap R L r ∈ B) → w ∈ B) :
    IsIntegral R w := by
  let A : Subring L := (algebraMap R L).range
  letI : Algebra R A := (algebraMap R L).rangeRestrict.toAlgebra
  letI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hw : w ∈ (integralClosure A L).toSubring := by
    have heq := iInf_valuationSubring_superset (s := (A : Set L))
    rw [Subring.closure_eq] at heq
    rw [← heq]
    exact Subring.mem_iInf.mpr fun B => h B.val fun r => B.property ⟨r, rfl⟩
  have hw' : IsIntegral A w := hw
  letI : Algebra.IsIntegral R A := Algebra.isIntegral_of_surjective (by
    rintro ⟨a, r, hr⟩
    exact ⟨r, Subtype.ext hr⟩)
  exact isIntegral_trans w hw'

end
end Dubon2026.SourceCurve.ConstantField
