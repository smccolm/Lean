import Dubon2026.SourceEllipticLegendreFaithfulModel
import Dubon2026.SourceEllipticLegendreGaloisField

/-! The finite Galois Legendre good-model stage and its faithful inertia.
The generators are the actual two-torsion abscissae and square roots of
their nonzero differences. This realizes the model and action required by
the positive-characteristic exceptional-fiber census, reverse genus and
good reduction in DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, finite Legendre model proof.
Native valuation-ring inertia and the existing explicit good model are reused.
No characteristic-zero Hahn-series route is introduced. -/
namespace Dubon2026.SourceEllipticLegendreStage
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial
open Dubon2026.SourceEllipticLegendre
open scoped Pointwise
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
theorem exists_galois_good_model_faithful [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] (h2 : (2 : F) ≠ 0) :
    ∃ S : IntermediateField F Ω, FiniteDimensional F S ∧ IsGalois F S ∧
      ∀ (M : IntermediateField F Ω), S ≤ M →
      ∀ (A : ValuationSubring M), IsUnit (2 : A) → algebraMap F M E.j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
        κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (∀ P : (E.baseChange M).toAffine.Point, 2 • P = 0 →
              Point.map (σ : M →ₐ[F] M) P = P) →
          (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
              g.map (residue A) = 1) →
          ∀ x : M, (x : Ω) ∈ S → σ x = x := by
  obtain ⟨e₁, e₂, e₃, h3, -⟩ := exists_roots (Ω := Ω) E h2
  obtain ⟨hfd, hgal⟩ := exists_S (E := E) h2 h3
  exact ⟨IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω), hfd, hgal,
    fun M hM A h2A hjA => model_and_faithful h2 h3 M hM A h2A hjA⟩


end
end Dubon2026.SourceEllipticLegendreStage
