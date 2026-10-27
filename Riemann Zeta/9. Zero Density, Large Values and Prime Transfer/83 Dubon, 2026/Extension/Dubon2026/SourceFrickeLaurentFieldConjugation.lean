import Dubon2026.SourceFrickeLaurentCyclotomicConjugation
import Dubon2026.SourceFrickeLaurentGeneratorIntegrality

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> analytic realization of cyclotomic conjugation. The original
cyclotomic Laurent field is stable under coefficient automorphisms, and
monic integrality over the original j algebra is preserved. These are the
inputs consumed by the existing holomorphic Fricke realization theorem. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

/-- The original j and Fricke Laurent generators over their cyclotomic field. -/
def frickeLaurentGeneratorsK (N : ℕ) [NeZero N] : Set (LaurentSeries (kN N)) :=
  insert (jqNModC (kN N) N) (Set.range (frickeLaurentK N))

theorem coeffMap_frickeLaurentGeneratorsK_aut (N : ℕ) [NeZero N]
    (σ : kN N ≃ₐ[ℚ] kN N) {X : LaurentSeries (kN N)}
    (hX : X ∈ frickeLaurentGeneratorsK N) :
    coeffMap σ.toRingEquiv.toRingHom X ∈ frickeLaurentGeneratorsK N := by
  obtain ⟨s, hs, hσ⟩ := exists_cyclotomic_aut_exponent N σ
  rcases hX with rfl | ⟨i, rfl⟩
  · rw [coeffMap_jqNModC_aut]
    exact Set.mem_insert _ _
  · rw [coeffMap_frickeLaurentK_aut N σ s hs hσ]
    exact Set.mem_insert_of_mem _ ⟨_, rfl⟩

theorem coeffMap_frickeLaurentFieldK_aut (N : ℕ) [NeZero N]
    (σ : kN N ≃ₐ[ℚ] kN N) {X : LaurentSeries (kN N)}
    (hX : X ∈ IntermediateField.adjoin (kN N) (frickeLaurentGeneratorsK N)) :
    coeffMap σ.toRingEquiv.toRingHom X ∈
      IntermediateField.adjoin (kN N) (frickeLaurentGeneratorsK N) := by
  induction hX using IntermediateField.adjoin_induction with
  | mem x hx => exact IntermediateField.subset_adjoin _ _ (coeffMap_frickeLaurentGeneratorsK_aut N σ hx)
  | algebraMap c =>
    simpa only [SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single] using
      (IntermediateField.algebraMap_mem
        (IntermediateField.adjoin (kN N) (frickeLaurentGeneratorsK N)) (σ c))
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | inv x _ hx => simpa only [map_inv₀] using inv_mem hx
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy

theorem coeffMap_frickeLaurentFieldK_inclusion (N : ℕ) [NeZero N]
    {X : LaurentSeries (kN N)}
    (hX : X ∈ IntermediateField.adjoin (kN N) (frickeLaurentGeneratorsK N)) :
    coeffMap (algebraMap (kN N) ℂ) X ∈
      IntermediateField.adjoin (kN N) (frickeLaurentGenerators N) := by
  induction hX using IntermediateField.adjoin_induction with
  | mem x hx =>
    apply IntermediateField.subset_adjoin
    rcases hx with rfl | ⟨i, rfl⟩
    · rw [coeffMap_jqNModC_kN]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
  | algebraMap c =>
    rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single]
    have hc := IntermediateField.algebraMap_mem
      (IntermediateField.adjoin (kN N) (frickeLaurentGenerators N)) c
    change algebraMap ℂ (LaurentSeries ℂ) (c : ℂ) ∈ _ at hc
    simpa only [SourceDifferential.algebraMap_laurentSeries_apply_alt] using hc
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | inv x _ hx => simpa only [map_inv₀] using inv_mem hx
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy

theorem coeffMap_jAlgebraK_aut (N : ℕ) [NeZero N] (σ : kN N ≃ₐ[ℚ] kN N)
    {X : LaurentSeries (kN N)}
    (hX : X ∈ Algebra.adjoin (kN N) ({jqNModC (kN N) N} : Set (LaurentSeries (kN N)))) :
    coeffMap σ.toRingEquiv.toRingHom X ∈
      Algebra.adjoin (kN N) ({jqNModC (kN N) N} : Set (LaurentSeries (kN N))) := by
  induction hX using Algebra.adjoin_induction with
  | mem x hx =>
    rcases Set.mem_singleton_iff.mp hx with rfl
    rw [coeffMap_jqNModC_aut]
    exact Algebra.self_mem_adjoin_singleton _ _
  | algebraMap c =>
    simpa only [SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single] using
      (Subalgebra.algebraMap_mem
        (Algebra.adjoin (kN N) ({jqNModC (kN N) N} : Set (LaurentSeries (kN N)))) (σ c))
  | add x y _ _ hx hy => simpa only [map_add] using Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => simpa only [map_mul] using Subalgebra.mul_mem _ hx hy

theorem isIntegral_jAlgebraK_coeffMap_aut (N : ℕ) [NeZero N]
    (σ : kN N ≃ₐ[ℚ] kN N) {X : LaurentSeries (kN N)}
    (hX : IsIntegral (Algebra.adjoin (kN N)
      ({jqNModC (kN N) N} : Set (LaurentSeries (kN N)))) X) :
    IsIntegral (Algebra.adjoin (kN N)
      ({jqNModC (kN N) N} : Set (LaurentSeries (kN N))))
      (coeffMap σ.toRingEquiv.toRingHom X) := by
  let R := Algebra.adjoin (kN N) ({jqNModC (kN N) N} : Set (LaurentSeries (kN N)))
  let φ := coeffMap σ.toRingEquiv.toRingHom
  let ψ : R →+* R :=
    { toFun := fun x => ⟨φ x, coeffMap_jAlgebraK_aut N σ x.property⟩
      map_zero' := Subtype.ext (map_zero φ)
      map_one' := Subtype.ext (map_one φ)
      map_add' := fun x y => Subtype.ext (map_add φ (x : LaurentSeries (kN N)) (y : LaurentSeries (kN N)))
      map_mul' := fun x y => Subtype.ext (map_mul φ (x : LaurentSeries (kN N)) (y : LaurentSeries (kN N))) }
  exact IsIntegral.map_of_comp_eq ψ φ (by ext x; rfl) hX

end
end Dubon2026.SourceFricke
