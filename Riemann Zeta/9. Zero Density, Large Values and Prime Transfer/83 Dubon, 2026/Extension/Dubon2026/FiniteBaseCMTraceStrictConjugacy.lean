import Dubon2026.FiniteBaseCMResidualPresentation
import Dubon2026.OriginalResidualTraceStrictConjugacy

/-! Equal traces on the original arithmetic CM subgroup determine actual
continuous lifts up to strict conjugacy. Arithmetic character finiteness
discharges the presentation input needed for DUB-17's polarization descent. -/

namespace Dubon2026
open Matrix
open scoped NumberField
noncomputable section

/-- Preserve the original rational algebra on the arithmetic extension. -/
local instance finiteBaseCMTraceConjugacyUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {ι O A L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A]
  [TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- On the actual CM arithmetic group, identical whole-group traces and the
same absolutely irreducible residual matrices give a strict conjugator;
finite generation of the residual quotient is derived, not supplied. -/
theorem finiteBaseCM_trace_eq_strictlyConjugate
    (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] (K : IntermediateField F (rationalUnramifiedExtension a))
    [Algebra.IsQuadraticExtension F K]
    (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (σ : finiteBaseCMProfiniteGroup a F K →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [hσirr : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))]
    (τ₁ τ₂ : finiteBaseCMProfiniteGroup a F K →ₜ* GeneralLinearGroup ι A)
    (h₁ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ₁.toMonoidHom = σ)
    (h₂ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ₂.toMonoidHom = σ)
    (htrace : ∀ x, Matrix.trace (τ₁ x).val = Matrix.trace (τ₂ x).val) (i₀ : ι) :
    MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
      τ₁.toMonoidHom τ₂.toMonoidHom := by
  obtain ⟨S, hS⟩ := finiteBaseCMResidual_has_profinite_presentation a F K ha p hp hpa σ hσ
  exact originalResidual_trace_eq_strictlyConjugate (L := L) hA eA p hp
    (finiteBaseCMProfiniteGroup a F K) σ hσ S hS τ₁ τ₂ h₁ h₂ htrace i₀

end
end Dubon2026
