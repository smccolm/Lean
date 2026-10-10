import Dubon2026.CompletedResidualCompactness
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! # Compact topology of original complete Noetherian local coefficient rings -/

namespace Dubon2026

noncomputable section

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Finite (IsLocalRing.ResidueField A)]

omit [IsNoetherianRing A] [Finite (IsLocalRing.ResidueField A)] in
/-- The genuine maximal-adic topology of any original complete local coefficient ring is Hausdorff. -/
theorem completeLocalAdic_t2Space
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A) : T2Space A := by
  have hcomplete : IsAdicComplete (WithIdeal.i : Ideal A) A := by
    rw [hA]
    infer_instance
  letI := hcomplete
  exact (IsAdic.isHausdorff_iff (I := (WithIdeal.i : Ideal A)) rfl).mp inferInstance

/-- Original complete Noetherian local coefficients with finite residue field are compact in their genuine maximal-adic topology. -/
theorem completeLocalAdic_compactSpace
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A) : CompactSpace A := by
  letI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField A))
  have hcomplete : IsAdicComplete (WithIdeal.i : Ideal A) A := by
    rw [hA]
    infer_instance
  letI := hcomplete
  letI : CompleteSpace A :=
    (IsAdic.isPrecomplete_iff (I := (WithIdeal.i : Ideal A)) rfl).mp inferInstance
  apply adic_compactSpace_of_finite_quotients
  intro n
  rw [hA]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A)) n

end
end Dubon2026
