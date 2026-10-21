import Dubon2026.SourcePrimeTwistedMinpolyRoot
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! DUB-17/18 -> numerical modular genus -> all-level degree
-> next-series nonmembership -> extension of the actual twisted embedding.
Native simple-extension homomorphisms and scalar restriction transport a
proved minimal-polynomial root to the literal field adjoin. A finite power
basis proves that the extended image stays in the required expansion range.
This replaces the separate adjoin-induction field construction in the
selected source's chain_extend argument.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux
variable {K : Type*} [Field K]
variable {E : Type*} [Field E] [Algebra ℚ E]

theorem extend_simple_embedding_in_expansion_range
    (F : IntermediateField ℚ E) (σ : F →+* LaurentSeries K)
    (x : E) (hx : IsIntegral F x)
    (y : LaurentSeries K) (hy : ((minpoly F x).map σ).eval y = 0)
    (e : ℕ) [NeZero e]
    (hrange : ∀ z : F, σ z ∈ (qExpand K e).range)
    (hyrange : y ∈ (qExpand K e).range) :
    let G := IntermediateField.adjoin ℚ ((F : Set E) ∪ {x})
    ∃ τ : G →+* LaurentSeries K,
      (∀ (z : F) (hz : (z : E) ∈ G), τ ⟨z, hz⟩ = σ z) ∧
      (∀ hxG : x ∈ G, τ ⟨x, hxG⟩ = y) ∧
      ∀ z : G, τ z ∈ (qExpand K e).range := by
  classical
  intro G
  letI : Algebra ℚ G := G.algebra'
  letI : Algebra F (LaurentSeries K) := σ.toAlgebra
  have halg : algebraMap F (LaurentSeries K) = σ := RingHom.algebraMap_toAlgebra σ
  let S := IntermediateField.adjoin F ({x} : Set E)
  have hyroots : y ∈ (minpoly F x).aroots (LaurentSeries K) := by
    apply (Polynomial.mem_roots ((minpoly.monic hx).map _).ne_zero).mpr
    exact hy
  let ψ : S →ₐ[F] LaurentSeries K :=
    (IntermediateField.algHomAdjoinIntegralEquiv F hx).symm ⟨y, hyroots⟩
  have hψ : ψ (IntermediateField.AdjoinSimple.gen F x) = y :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen F hx ⟨y, hyroots⟩
  have he : S.restrictScalars ℚ = G := IntermediateField.restrictScalars_adjoin ℚ F {x}
  letI : Algebra ℚ (S.restrictScalars ℚ) := (S.restrictScalars ℚ).algebra'
  let ι : G →+* S := (IntermediateField.equivOfEq he.symm).toRingHom
  refine ⟨ψ.toRingHom.comp ι, ?_, ?_, ?_⟩
  · intro z hz
    change ψ (ι ⟨z, hz⟩) = σ z
    have h : ι ⟨z, hz⟩ = algebraMap F S z := Subtype.ext rfl
    rw [h, AlgHom.commutes, halg]
  · intro hxG
    change ψ (ι ⟨x, hxG⟩) = y
    have h : ι ⟨x, hxG⟩ = IntermediateField.AdjoinSimple.gen F x := Subtype.ext rfl
    rw [h, hψ]
  · intro z
    change ψ (ι z) ∈ (qExpand K e).range
    obtain ⟨g, hg⟩ := (IntermediateField.adjoin.powerBasis hx).exists_eq_aeval' (ι z)
    rw [IntermediateField.adjoin.powerBasis_gen] at hg
    rw [hg, ← Polynomial.aeval_algHom_apply, hψ, Polynomial.aeval_def,
      Polynomial.eval₂_eq_sum_range]
    refine sum_mem fun i _ => mul_mem ?_ (pow_mem hyrange i)
    rw [halg]
    exact hrange _

end
end Dubon2026.SourceFunctionField
