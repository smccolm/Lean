import Dubon2026.RationalPrimeCyclotomicResidualReduction

namespace Dubon2026
noncomputable section

open IsCyclotomicExtension

set_option maxHeartbeats 1200000

/-- Adjoining the image of a cyclotomic field to a larger base inside one
ambient field remains cyclotomic of the same order. -/
theorem embeddedFiniteGaloisCompositum_isCyclotomic_of_primitiveRoot
    {R K L Ω : Type} [Field R] [Field K] [Field L] [Field Ω]
    [Algebra R K] [Algebra R L] [Algebra K Ω] [Algebra R Ω]
    [IsScalarTower R K Ω] [FiniteDimensional R L] [IsGalois R L]
    (i : L →ₐ[R] Ω) (n : ℕ) [NeZero n]
    [IsCyclotomicExtension {n} R L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) :
    IsCyclotomicExtension {n} K (embeddedFiniteGaloisCompositum (K := K) i) := by
  let M := embeddedFiniteGaloisCompositum (K := K) i
  have hμ : IsPrimitiveRoot (i ζ) n := hζ.map_of_injective i.injective
  apply (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
    n K Ω M.toIntermediateField hμ).mpr
  change IntermediateField.adjoin K (Set.range i) =
    IntermediateField.adjoin K {i ζ}
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Algebra.adjoin R ({ζ} : Set L) := by
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
      trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff.mp hy]
        exact IntermediateField.subset_adjoin K {i ζ} (Set.mem_singleton (i ζ))
    | algebraMap r =>
        rw [i.commutes, IsScalarTower.algebraMap_apply R K Ω]
        exact (IntermediateField.adjoin K {i ζ}).algebraMap_mem _
    | add x y _ _ hx hy =>
        simpa only [map_add] using (IntermediateField.adjoin K {i ζ}).add_mem hx hy
    | mul x y _ _ hx hy =>
        simpa only [map_mul] using (IntermediateField.adjoin K {i ζ}).mul_mem hx hy
  · apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact IntermediateField.subset_adjoin K (Set.range i) ⟨ζ, rfl⟩

end
end Dubon2026
