import Dubon2026.FiniteBaseCMTraceStrictConjugacy
import Dubon2026.FiniteBaseCMConjugation
import Dubon2026.PolarizedTwistedDual
import Dubon2026.LocalCoefficientMatrixLifting
import Dubon2026.MatrixRepresentationConjugation

/-! Construct the actual conjugate-duality matrix over complete local CM
coefficients from the proved equal-trace criterion. The residual matrix is
lifted by the native local GL surjectivity theorem. This is the matrix
existence step of DUB-17 polarization descent; symmetry is separate. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Preserve the original rational algebra in the arithmetic CM comparison. -/
local instance finiteBaseCMIntertwinerUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {ι O A L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A]
  [TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]
  (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]

/-- Actual conjugate-dual trace equality constructs a coefficient-ring
intertwiner with the specified residual polarization. Arithmetic character
finiteness supplies the presentation, and residual absolute irreducibility
supplies strict conjugacy; no coefficient-ring intertwiner is assumed. -/
theorem finiteBaseCM_polarizationIntertwiner_exists
    (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (hA : IsAdic (IsLocalRing.maximalIdeal A))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (σ : finiteBaseCMProfiniteGroup a F K →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [hσirr : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))]
    (τ : finiteBaseCMProfiniteGroup a F K →ₜ* GeneralLinearGroup ι A)
    (μ : finiteBaseCMProfiniteGroup a F K →ₜ* Aˣ)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ)
    (Bbar : GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hbar : σ.comp (finiteBaseCMConjugation a F K).toMonoidHom =
      matrixRepresentationConjugate (polarizedTwistedDual σ
        ((Units.map (localCoefficientReduction eA).toMonoidHom).comp μ.toMonoidHom)) Bbar)
    (htrace : ∀ x, Matrix.trace (τ (finiteBaseCMConjugation a F K x)).val =
      Matrix.trace (polarizedTwistedDual τ.toMonoidHom μ.toMonoidHom x).val) (i₀ : ι) :
    ∃ B : GeneralLinearGroup ι A,
      GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom B = Bbar ∧
      ∀ x, τ (finiteBaseCMConjugation a F K x) =
        B * polarizedTwistedDual τ.toMonoidHom μ.toMonoidHom x * B⁻¹ := by
  let r := (localCoefficientReduction eA).toRingHom
  letI : IsLocalHom r := inferInstanceAs
    (IsLocalHom (eA.toRingHom.comp (IsLocalRing.residue A)))
  obtain ⟨B₀, hB₀⟩ := generalLinearGroup_map_surjective r (localCoefficientReduction_surjective eA) Bbar
  let δ := polarizedTwistedDual τ.toMonoidHom μ.toMonoidHom
  have hδ : Continuous δ := polarizedTwistedDual_continuous _ _ τ.continuous μ.continuous
  let τ₁ : finiteBaseCMProfiniteGroup a F K →ₜ* GeneralLinearGroup ι A :=
    ⟨matrixRepresentationConjugate δ B₀, matrixRepresentationConjugate_continuous δ hδ B₀⟩
  let τ₂ := τ.comp (finiteBaseCMConjugation a F K)
  let σc := σ.comp (finiteBaseCMConjugation a F K).toMonoidHom
  have hσc : Continuous σc := hσ.comp (finiteBaseCMConjugation a F K).continuous
  have hic : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σc)) :=
    @finiteBaseCMConjugate_absoluteIrreducible a F _ _ K _ _
      ι (IsLocalRing.ResidueField O) L _ _ _ _ _ σ hσirr
  have h₁ : (GeneralLinearGroup.map r).comp τ₁.toMonoidHom = σc := by
    change (GeneralLinearGroup.map r).comp (matrixRepresentationConjugate δ B₀) = σc
    rw [matrixRepresentationConjugate_map, polarizedTwistedDual_map, hτ, hB₀]
    exact hbar.symm
  have h₂ : (GeneralLinearGroup.map r).comp τ₂.toMonoidHom = σc := by
    change ((GeneralLinearGroup.map r).comp τ.toMonoidHom).comp
      (finiteBaseCMConjugation a F K).toMonoidHom = σc
    rw [hτ]
  have ht : ∀ x, Matrix.trace (τ₁ x).val = Matrix.trace (τ₂ x).val := by
    intro x
    exact (Matrix.trace_units_conj B₀ (δ x).val).trans (htrace x).symm
  obtain ⟨U, hU, he⟩ := finiteBaseCM_trace_eq_strictlyConjugate (L := L) (hσirr := hic)
    a F K ha p hp hpa hA eA σc hσc τ₁ τ₂ h₁ h₂ ht i₀
  refine ⟨U * B₀, ?_, ?_⟩
  · rw [map_mul, hU, hB₀, one_mul]
  · intro x
    calc
      _ = U * (B₀ * δ x * B₀⁻¹) * U⁻¹ := he x
      _ = _ := by dsimp only [δ]; group

end
end Dubon2026
