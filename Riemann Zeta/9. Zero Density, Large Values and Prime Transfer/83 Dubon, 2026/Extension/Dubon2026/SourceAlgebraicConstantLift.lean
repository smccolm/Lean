import Dubon2026.SourceAlgebraicConstantRoots

/-! DUB-17/18 -> original all-weight arithmetic association -> actual
Gamma1 character realization -> differential/cusp comparison -> rational
Fourier spanning -> integral base change of Fricke fractions. The algebraic
constant-adjoining step expresses an integral element as a complex span of
integral elements over the original constants. Finite extension embeddings
and Lagrange interpolation discharge integrality of the actual coordinates.
Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsIntegral_mem_span_of_adjoin_simple_constants. No proof limit is raised.
The later consumer is the actual Fricke fraction field; constant-extension
spanning and rational Fourier realization are not assumed. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open Polynomial
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℂ K]
variable (F : IntermediateField ℚ ℂ) (B S : Set K)
variable {B S}

theorem algebraMap_adjoinF_mem {c : ℂ} {z : ℂ} (hz : z ∈ IntermediateField.adjoin ↥F {c}) :
    algebraMap ℂ K z ∈
      IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c} := by
  set f := IsScalarTower.toAlgHom ↥F ℂ K
  have h1 : algebraMap ℂ K z ∈ (IntermediateField.adjoin ↥F {c}).map f := by
    rw [← SetLike.mem_coe, IntermediateField.coe_map]
    exact ⟨z, hz, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton] at h1
  have h2 : IntermediateField.adjoin ↥F {f c} ≤
      (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).restrictScalars ↥F :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.mem_adjoin_simple_self ↥(KFld F S) _))
  exact h2 h1

theorem closure_adjoin_le {c : ℂ} :
    Subfield.closure
        (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S) ≤
      (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).toSubfield := by
  refine Subfield.closure_le.mpr ?_
  rintro y (⟨z, hz, rfl⟩ | hy)
  · exact algebraMap_adjoinF_mem F hz
  · exact (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).algebraMap_mem
      ⟨y, IntermediateField.subset_adjoin ↥F S hy⟩

variable (B) in

theorem exists_lift_of_mem_adjoin (hBS : B ⊆ S) {c : ℂ} (hc : IsIntegral ↥F c) {y : K}
    (hy : y ∈ Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) B) :
    ∃ y' : ↥(IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}),
      (y' : K) = y ∧
      ∀ φ : ↥(IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}) →ₐ[↥(KFld F S)] K,
        φ y' ∈ Algebra.adjoin ↥(TRng F B) {φ (IntermediateField.AdjoinSimple.gen ↥(KFld F S)
          (algebraMap ℂ K c))} := by
  set ι := algebraMap ℂ K
  set L₀ := KFld F S
  set E := IntermediateField.adjoin ↥L₀ {ι c}
  set g := IntermediateField.AdjoinSimple.gen ↥L₀ (ι c)
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨algebraMap ↥L₀ ↥E ⟨x, IntermediateField.subset_adjoin ↥F S (hBS hx)⟩, rfl, fun φ ↦ ?_⟩
    rw [AlgHom.commutes]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin ↥(TRng F B) {φ g})
      (⟨x, Algebra.subset_adjoin hx⟩ : ↥(TRng F B))
  | algebraMap z =>
    have hz : (z : ℂ) ∈ IntermediateField.adjoin ↥F {c} := z.2
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hc.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨u, hu⟩ := hz
    refine ⟨Polynomial.aeval g (u.map (algebraMap ↥F ↥L₀)), ?_, fun φ ↦ ?_⟩
    · rw [algebraMap_subfield_apply', ← IntermediateField.aeval_coe,
        Polynomial.aeval_map_algebraMap, IntermediateField.AdjoinSimple.coe_gen,
        Polynomial.aeval_algebraMap_apply]
      exact congrArg ι hu
    · rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap,
        ← Polynomial.aeval_map_algebraMap ↥(TRng F B)]
      exact Polynomial.aeval_mem_adjoin_singleton _ _
  | add x y _ _ ihx ihy =>
    obtain ⟨x', hx', hx⟩ := ihx
    obtain ⟨y', hy', hy⟩ := ihy
    exact ⟨x' + y', by rw [IntermediateField.coe_add, hx', hy'], fun φ ↦ by
      rw [map_add]; exact Subalgebra.add_mem _ (hx φ) (hy φ)⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨x', hx', hx⟩ := ihx
    obtain ⟨y', hy', hy⟩ := ihy
    exact ⟨x' * y', by rw [IntermediateField.coe_mul, hx', hy'], fun φ ↦ by
      rw [map_mul]; exact Subalgebra.mul_mem _ (hx φ) (hy φ)⟩


end
end Dubon2026.SourceFricke.ConstantDescent
