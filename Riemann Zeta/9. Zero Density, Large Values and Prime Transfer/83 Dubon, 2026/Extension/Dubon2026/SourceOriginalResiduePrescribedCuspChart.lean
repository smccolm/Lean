import Dubon2026.SourcePrescribedPrimitiveRootReduction
import Dubon2026.SourceOriginalResidueSlashFieldEmbedding
import Dubon2026.SourceGammaOneResidueSeparability

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> prescribed residue cusp charts. The actual
valuation residue field is algebraically closed. Construct its reduction of all
complex algebraic integers with the prescribed primitive-root image, and use
that reduction in the actual full original Gamma1 function-field embedding.
Its original j coordinate has exactly the width-N image j(q^N). No coefficient
reduction map, field embedding, degree or algebraicity certificate is an input.
Diamond-stabilizer equivariance and the resulting fiber bounds remain required. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups
local notation "Zbar" => integralClosure ℤ ℂ
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
private local instance : Algebra kk (qExpFunctionFieldC kk (Gamma1 N)) :=
  (qExpFunctionFieldC kk (Gamma1 N)).toSubalgebra.algebra

theorem exists_originalResiduePrescribedCuspFieldHom (hℓN : ¬ ℓ ∣ N)
    (ζ : kk) (hζ : IsPrimitiveRoot ζ N) (β : SL(2, ℤ)) :
    ∃ (φ : Zbar →+* kk) (hN : (N : kk) ≠ 0)
      (Φ : qExpFunctionFieldC kk (Gamma1 N) →ₐ[kk] LaurentSeries kk),
      (∀ z : Zbar, (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N) → φ z = ζ) ∧
      (∀ x (hx : x ∈ normalizedGenerators N kk),
        Φ ⟨x, normalizedGenerators_subset N kk hx⟩ = normalizedSlashValue N φ hN β x) ∧
      Φ ⟨jqModC kk, jqModC_mem_integralRatioField kk (Gamma1 N)⟩ = qExpand kk N (jqModC kk) := by
  letI := valuation_residue_isAlgClosed A
  obtain ⟨φ, hφ⟩ := exists_algebraicIntegerReduction_primitiveRoot N ℓ hℓN kk ζ hζ
  obtain ⟨hN, Φ, hΦ⟩ := exists_originalResidueSlashFieldHom A N ℓ hℓN φ β
  refine ⟨φ, hN, Φ, hφ, hΦ, ?_⟩
  exact (hΦ (jqModC kk) (jqModC_mem_normalizedGenerators N kk)).trans
    (normalizedSlashValue_jqModC N ℓ φ hN β)

end
end Dubon2026.SourceFunctionField.IntegralSlash
