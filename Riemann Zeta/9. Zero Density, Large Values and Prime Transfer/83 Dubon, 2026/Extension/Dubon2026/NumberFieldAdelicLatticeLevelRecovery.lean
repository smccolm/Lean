import Dubon2026.NumberFieldAdelicLatticeTransport

/-! # Recovering the actual integral adelic level from original lattice transport

Transport of the original lattices in both directions proves integrality
of the relative matrix and its inverse at every original finite place.
This recovers membership in the actual compact open integral matrix
level and supplies DUB-17's unitary arithmetic double-coset comparison.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Matrix

variable (K : Type*) [Field K] [NumberField K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Transport between the original attached lattices recovers the exact integral matrix level. -/
theorem numberFieldAdelicLattice_level_recovery (U : Matrix.GeneralLinearGroup ι K)
    (g h : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (hU : U.val.mulVec '' (numberFieldAdelicLattice K ι g : Set (ι → K)) =
      numberFieldAdelicLattice K ι h) :
    h⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)) U * g ∈
      numberFieldIntegralMatrixLevel K ι := by
  have hf : ∀ x ∈ numberFieldAdelicLattice K ι g,
      U.val.mulVec x ∈ numberFieldAdelicLattice K ι h := by
    intro x hx
    change U.val.mulVec x ∈ (numberFieldAdelicLattice K ι h : Set (ι → K))
    rw [← hU]
    exact ⟨x, hx, rfl⟩
  have hi : ∀ x ∈ numberFieldAdelicLattice K ι h,
      (U⁻¹).val.mulVec x ∈ numberFieldAdelicLattice K ι g := by
    intro x hx
    change x ∈ (numberFieldAdelicLattice K ι h : Set (ι → K)) at hx
    rw [← hU] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
    exact hz
  apply (numberFieldIntegralMatrixLevel_mem_iff K ι _).mpr
  constructor
  · intro i j v
    exact numberFieldAdelicLattice_transport_integral K ι U g h hf i j v
  · intro i j v
    have hz := numberFieldAdelicLattice_transport_integral K ι U⁻¹ h g hi i j v
    simpa only [_root_.mul_inv_rev, inv_inv, map_inv, mul_assoc] using hz

end
end Dubon2026
