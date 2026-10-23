import Dubon2026.SourceModularCoefficientJFiberDegree

/-! Finite-set degree sums for actual j fibers and poles. These reuse the
existing separating-coordinate formula and all-level field degree, and
supply the multiplicity terms in the DUB-17/18 reverse genus inequality. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve IntermediateField
open scoped IntermediateField

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- The actual total j-pole order is psi(N). -/
theorem sum_coeff_j_pole_orders_eq_psi (hNK : (N : K) ≠ 0) :
    (∑ᶠ v : {v : Place K (modularFunctionFieldCoeff N K) // v.ord (jCoeff N K) < 0},
      -v.1.ord (jCoeff N K)) = (SourceLevelProjective.dedekindPsi N : ℤ) := by
  have ht : Transcendental K (jCoeff N K)⁻¹ :=
    fun h => transcendental_jCoeff N K (IsAlgebraic.inv_iff.mp h)
  haveI : FiniteDimensional K⟮(jCoeff N K)⁻¹⟯ (modularFunctionFieldCoeff N K) := by
    rw [adjoin_singleton_inv_eq]
    exact finiteDimensional_coeff_field N K
  haveI : Algebra.IsSeparable K⟮(jCoeff N K)⁻¹⟯ (modularFunctionFieldCoeff N K) := by
    rw [adjoin_singleton_inv_eq]
    exact isSeparable_coeff_field N K
  have h := sum_positive_orders_eq_finrank_separating _ ht
  have hr : ∀ v : Place K (modularFunctionFieldCoeff N K), Module.finrank K v.ResidueField = 1 :=
    fun v => Module.finrank_of_bijective_algebraMap (coeff_place_residue_algebraMap_bijective N K v)
  simp only [hr, Nat.cast_one, mul_one] at h
  rw [adjoin_singleton_inv_eq, finrank_coeff_over_j_eq_psi N hNK] at h
  let e : {v : Place K (modularFunctionFieldCoeff N K) // 0 < v.ord (jCoeff N K)⁻¹} ≃
      {v : Place K (modularFunctionFieldCoeff N K) // v.ord (jCoeff N K) < 0} :=
    Equiv.subtypeEquivRight fun v => by rw [v.ord_inv, neg_pos]
  rw [← finsum_comp_equiv e]
  change (∑ᶠ v : {v : Place K (modularFunctionFieldCoeff N K) // 0 < v.ord (jCoeff N K)⁻¹},
    -v.1.ord (jCoeff N K)) = _
  simpa only [Place.ord_inv] using h

/-- Every complete finite j fiber has the computed total multiplicity. -/
theorem sum_coeff_j_fiber_orders_finset (hNK : (N : K) ≠ 0) (c : K)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c)) :
    (∑ v ∈ S, v.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c)) =
      (SourceLevelProjective.dedekindPsi N : ℤ) := by
  have h := sum_coeff_j_fiber_orders_eq_psi N K hNK c
  have he : {v : Place K (modularFunctionFieldCoeff N K) |
      0 < v.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c)} = (S : Set _) :=
    Set.ext fun v => (hS v).symm
  have h' := (finsum_set_coe_eq_finsum_mem
    (f := fun v : Place K (modularFunctionFieldCoeff N K) =>
      v.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c))
    {v | 0 < v.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c)}).symm.trans h
  rw [he, finsum_mem_coe_finset] at h'
  exact h'

/-- The full finite pole set has the computed total pole order. -/
theorem sum_coeff_j_pole_orders_finset (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v, v ∈ S ↔ v.ord (jCoeff N K) < 0) :
    (∑ v ∈ S, -v.ord (jCoeff N K)) = (SourceLevelProjective.dedekindPsi N : ℤ) := by
  have h := sum_coeff_j_pole_orders_eq_psi N K hNK
  have he : {v : Place K (modularFunctionFieldCoeff N K) | v.ord (jCoeff N K) < 0} =
      (S : Set _) := Set.ext fun v => (hS v).symm
  have h' := (finsum_set_coe_eq_finsum_mem
    (f := fun v : Place K (modularFunctionFieldCoeff N K) => -v.ord (jCoeff N K))
    {v | v.ord (jCoeff N K) < 0}).symm.trans h
  rw [he, finsum_mem_coe_finset] at h'
  exact h'

end Dubon2026.SourceFunctionField
