import Dubon2026.SourceEllipticDeuringFaithfulModel

/-! DUB-17/18 -> characteristic-two modular genus/Picard -> faithful good-model inertia.
The explicit generator argument is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero.
Existing local division-field restriction, torsion reduction and root separation
discharge the source interfaces. No proof-limit or linter override is used. -/
namespace Dubon2026.SourceEllipticDeuring
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial
open SourceEllipticDivisionField
open scoped Pointwise
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]

theorem exists_deuring_galois_model_faithful [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] (h3 : (3 : F) ≠ 0) :
    ∃ S : IntermediateField F Ω, FiniteDimensional F S ∧ IsGalois F S ∧
      ∀ (M : IntermediateField F Ω), S ≤ M →
      ∀ (A : ValuationSubring M), IsUnit (3 : A) → algebraMap F M E.j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
        κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (∀ P : (E.baseChange M).toAffine.Point, 3 • P = 0 →
              Point.map (σ : M →ₐ[F] M) P = P) →
          (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
              g.map (residue A) = 1) →
          ∀ x : M, (x : Ω) ∈ S → σ x = x := by
  obtain ⟨L, hLgal, hLfaith, hcoords, hfd, hgal⟩ := exists_S (Ω := Ω) E h3
  haveI := hLgal
  exact ⟨L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E), hfd, hgal,
    fun M hM A h3A hjA => model_and_faithful h3 L hLfaith hcoords M hM A h3A hjA⟩

end
end Dubon2026.SourceEllipticDeuring
