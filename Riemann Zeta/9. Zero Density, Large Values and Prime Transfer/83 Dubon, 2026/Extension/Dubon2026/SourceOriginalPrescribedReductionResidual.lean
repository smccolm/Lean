import Dubon2026.SourceOriginalPrescribedResidualFrobenius
import Dubon2026.SourceReductionCompletionLocalStructures
import Dubon2026.SourcePrescribedCompletionResidue
import Dubon2026.SourceRankTwoCharpolyCoefficients

/-! DUB-17/18 -> all-weight residual association -> prescribed reduction.
Construct the local coefficient field from the kernel of the given reduction,
apply the actual original Tate/lattice realization there, and embed its
residue representation into the prescribed target field. All original
Frobenius and inertia identities retain the exact reduced coefficients.
The arithmetic quotient and norm-local interface comparisons remain separate. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open IsDedekindDomain Matrix Polynomial
open scoped NumberField ValuativeRel
local notation "Qbar" => AlgebraicClosure ℚ
variable (N ell : ℕ) [NeZero N] (hell : ell.Prime) [Fact ell.Prime]
variable (K : Type) [Field K] [TopologicalSpace K] [CharP K ell]
variable (F : Type) [Field F] [NumberField F]
variable (f : PrimitiveCuspForm N 2) (iota : sourcePrimitiveCoefficientField f →ₐ[ℚ] F)
variable (φ : 𝓞 F →+* K)
local notation "w" => sourceReductionPrime F ell hell φ
local notation "E" => HeightOneSpectrum.adicCompletion F w
private local instance : CharZero E := Algebra.charZero_of_charZero F E
private local instance : Algebra ℚ_[ell] E :=
  (sourceReductionCompletionPadicMap F ell hell φ).toAlgebra
private local instance : ValuativeRel ℚ_[ell] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[ell]))
private local instance : ValuativeRel E :=
  ValuativeRel.ofValuation (NormedField.valuation (K := E))
private local instance : IsModuleTopology ℚ_[ell] E :=
  sourceReductionCompletion_isModuleTopology F ell hell φ
private local instance : IsNonarchimedeanLocalField E :=
  sourceReductionCompletion_isNonarchimedeanLocalField F ell hell φ
private local instance : (ValuativeRel.valuation ℚ_[ell]).HasExtension (ValuativeRel.valuation E) :=
  sourceReductionCompletion_hasExtension F ell hell φ
private local instance : TopologicalSpace 𝓀[E] :=
  inferInstanceAs (TopologicalSpace (𝒪[E] ⧸ IsLocalRing.maximalIdeal 𝒪[E]))

include hell in
theorem originalPrimitive_numberField_reduction_residual_realization :
    ∃ ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) K,
      Continuous ρ ∧ (Set.range ρ).Finite ∧
      (∀ q : ℕ, q.Prime → ¬q ∣ N * ell →
        ∀ A : ValuationSubring Qbar, (q : Qbar) ∈ A.nonunits →
          ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
            σ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype →
              ρ σ = 1) ∧
      ∀ q : ℕ, q.Prime → ¬q ∣ N * ell →
        ∀ A : ValuationSubring Qbar, (q : Qbar) ∈ A.nonunits →
          ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
            (∃ hd : σ ∈ A.decompositionSubgroup ℚ,
              ∀ z : IsLocalRing.ResidueField A,
                (⟨σ, hd⟩ : A.decompositionSubgroup ℚ) • z = z ^ q) →
            let a : 𝓞 F := ⟨iota (sourcePrimitiveFieldCoefficient f q),
              (sourcePrimitiveFieldCoefficient_isIntegral f (by norm_num) q).map (iota.restrictScalars ℤ)⟩
            (ρ σ).val.charpoly = X ^ 2 - C (φ a) * X + C (q : K) ∧
              (ρ σ).val.trace = φ a ∧ (ρ σ).val.det = (q : K) := by
  let τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E :=
    (algebraMap F E).toRatAlgHom.comp iota
  have hsrc := originalPrimitive_prescribed_residual_frobenius_realization N ell E f τ
  rcases hsrc with ⟨hf, hd, _, π, ρ, e, ρi, ρr, _, _, _, _, _, hcr, _, _, hin, hfr⟩
  letI : Finite 𝓀[E] := hf
  letI : DiscreteTopology 𝓀[E] := hd
  let ψ := sourcePrescribedCompletionResidueMap F ell hell φ
  let ρK := (GeneralLinearGroup.map ψ).comp ρr
  refine ⟨ρK, (continuous_of_discreteTopology.generalLinearGroup_map).comp hcr, ?_, ?_, ?_⟩
  · apply (Set.finite_range (GeneralLinearGroup.map ψ)).subset
    rintro _ ⟨σ, rfl⟩
    exact ⟨ρr σ, rfl⟩
  · intro q hq hNq A hA σ hσ
    change GeneralLinearGroup.map ψ (ρr σ) = 1
    rw [(hin q hq hNq A hA σ hσ).2.2, map_one]
  · intro q hq hNq A hA σ hσ
    let a : 𝓞 F := ⟨iota (sourcePrimitiveFieldCoefficient f q),
      (sourcePrimitiveFieldCoefficient_isIntegral f (by norm_num) q).map (iota.restrictScalars ℤ)⟩
    let b : 𝒪[E] := ⟨τ (sourcePrimitiveFieldCoefficient f q),
      sourcePrimitiveCoefficient_valuation_le_one f (by norm_num) τ q⟩
    have ha : ψ (IsLocalRing.residue 𝒪[E] b) = φ a :=
      sourcePrescribedCompletionResidueMap_integer F ell hell φ a
    have hp := (hfr q hq hNq A hA σ hσ).2.1
    have hpoly : (ρK σ).val.charpoly = X ^ 2 - C (φ a) * X + C (q : K) := by
      change ((ρr σ).val.map ψ).charpoly = _
      rw [Matrix.charpoly_map, hp]
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_natCast, map_natCast]
      rw [ha]
    exact ⟨hpoly, rank_two_trace_det_of_charpoly (ρK σ).val (φ a) (q : K) hpoly⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
