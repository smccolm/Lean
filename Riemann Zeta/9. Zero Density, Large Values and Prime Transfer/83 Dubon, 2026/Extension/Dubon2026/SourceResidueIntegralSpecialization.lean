import Dubon2026.SourceResidueRationalDenominators
import Dubon2026.SourceResidueClosedValuationField

/-! DUB-17/18 -> original Frobenius/inertia -> actual good/place reduction
-> coefficient specialization of the actual modular field. Powers of j_N
below psi(N) are independent in the residue field and span the characteristic-
zero field. Primitive polynomial reduction therefore preserves membership of
every integral Laurent series. No independence, degree, basis, generation or
closed-residue-field premise remains. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField SourceLevelProjective
open scoped IntermediateField

theorem coefficientMap_j_expansion {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (qExpand R N (jqModC R)) = qExpand S N (jqModC S) := by
  rw [coeffMap_qExpand]
  change qExpand S N ((jqModC R).map f) = _
  rw [map_jqModC]

theorem integral_modular_coefficient_specializes {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) (N : ℕ) [NeZero N]
    (hNL : (N : L) ≠ 0) (hNk : (N : IsLocalRing.ResidueField A) ≠ 0)
    (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldCoeff N L) :
    coeffMap (IsLocalRing.residue A) y ∈ modularFunctionFieldCoeff N (IsLocalRing.ResidueField A) := by
  classical
  let k := IsLocalRing.ResidueField A
  haveI : IsAlgClosed k := valuation_residue_isAlgClosed A
  obtain ⟨g, hg⟩ := residue_member_power_coordinates N hNL (coeffMap A.subtype y) hy
  obtain ⟨D, hD, c, hc⟩ := rational_j_clear_finite_denominators g
  have hrel : Polynomial.aeval (jqModC L) D * coeffMap A.subtype y =
      ∑ i, Polynomial.aeval (jqModC L) (c i) * (qExpand L N (jqModC L)) ^ (i : ℕ) := by
    simp_rw [hc, mul_assoc, ← Finset.mul_sum]
    rw [hg]
  obtain ⟨C, hCne, hC⟩ := integral_polynomial_relation_specializes A
    (fun o : Option (Fin (dedekindPsi N)) =>
      o.elim y (fun i => (qExpand A N (jqModC A)) ^ (i : ℕ)))
    (fun o => o.elim D (fun i => -c i)) ⟨none, hD⟩ (by
      rw [Fintype.sum_option]
      simp only [Option.elim, map_pow, coefficientMap_j_expansion, map_neg,
        neg_mul, Finset.sum_neg_distrib]
      rw [← hrel]
      ring)
  rw [Fintype.sum_option] at hC
  simp only [Option.elim, map_pow, coefficientMap_j_expansion] at hC
  have h0 : C none ≠ 0 := by
    intro he
    rw [he, map_zero, zero_mul, zero_add] at hC
    have hall := residue_power_polynomial_independent N hNk (fun i => C (some i)) hC
    obtain ⟨o, ho⟩ := hCne
    cases o with
    | none => exact ho he
    | some i => exact ho (hall i)
  have hCj : Polynomial.aeval (jqModC k) (C none) ≠ 0 := fun h =>
    transcendental_jqModC k ⟨C none, h0, h⟩
  have hyeq : coeffMap (IsLocalRing.residue A) y =
      -((Polynomial.aeval (jqModC k) (C none))⁻¹ *
        ∑ i, Polynomial.aeval (jqModC k) (C (some i)) *
          (qExpand k N (jqModC k)) ^ (i : ℕ)) := by
    have h1 := eq_neg_of_add_eq_zero_left hC
    calc _ = (Polynomial.aeval (jqModC k) (C none))⁻¹ *
        (Polynomial.aeval (jqModC k) (C none) * coeffMap (IsLocalRing.residue A) y) := by
          rw [← mul_assoc, inv_mul_cancel₀ hCj, one_mul]
      _ = _ := by rw [h1, mul_neg]
  have hpoly (P : Polynomial k) : Polynomial.aeval (jqModC k) P ∈ modularFunctionFieldCoeff N k :=
    (IntermediateField.adjoin_simple_le_iff.mpr (jq_mem_coeff_field N k))
      (IntermediateField.algebra_adjoin_le_adjoin k _ (Polynomial.aeval_mem_adjoin_singleton k _))
  rw [hyeq]
  exact neg_mem (mul_mem (inv_mem (hpoly _))
    (sum_mem fun i _ => mul_mem (hpoly _) (pow_mem (jqd_mem_coeff_field N k dvd_rfl) _)))

end
end Dubon2026.SourceFunctionField
