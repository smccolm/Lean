import Dubon2026.SourceOriginalPrescribedTateSpecialization
import Dubon2026.SourceOriginalResidualFrobeniusCharpoly
import Dubon2026.SourceOriginalResidualInertia

/-! DUB-17/18 -> all-weight residual association -> prescribed reduction.
Keep the supplied original Fourier-field embedding through the actual
Tate specialization, constructed stable lattice, integral basis and literal
residue reduction. The same resulting representation has the proved source
Frobenius and inertia identities. Choosing the local embedding compatible
with the source's prescribed algebraic-integer reduction remains separate. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open scoped ValuativeRel
open SourceCurve Matrix Polynomial
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]
variable (E : Type) [Field E] [Algebra ℚ_[ell] E] [CharZero E]
variable [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E]
variable [IsNonarchimedeanLocalField E] [IsModuleTopology ℚ_[ell] E]
private local instance : ValuativeRel ℚ_[ell] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[ell]))
private local instance : TopologicalSpace 𝓀[E] :=
  inferInstanceAs (TopologicalSpace (𝒪[E] ⧸ IsLocalRing.maximalIdeal 𝒪[E]))
variable [(ValuativeRel.valuation ℚ_[ell]).HasExtension (ValuativeRel.valuation E)]
private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem originalPrimitive_prescribed_residual_frobenius_realization
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    Finite 𝓀[E] ∧ DiscreteTopology 𝓀[E] ∧ CharP 𝓀[E] ell ∧
    ∃ (π : originalRationalTateModule N ell →ₗ[ℚ_[ell]] (Fin 2 → E))
      (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
      (e : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E))
      (ρint : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) 𝒪[E])
      (ρres : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) 𝓀[E]),
      Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
      (∀ (q : Nat.Primes) (x : originalRationalTateModule N ell),
        π ((TateModule.tateMap ell (originalHeckePicard Qbar N q.val)).baseChange ℚ_[ell] x) =
          (fun i => τ (sourcePrimitiveFieldCoefficient f q.val) * π x i)) ∧
      (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N ell),
        (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N ell σ x)) ∧
      Continuous ρint ∧ Continuous ρres ∧
      (∀ σ i j, (ρres σ).val i j = IsLocalRing.residue 𝒪[E] ((ρint σ).val i j)) ∧
      (∀ σ v, (ρint σ).val.map (algebraMap 𝒪[E] E) *ᵥ e v = e ((ρ σ).val *ᵥ v)) ∧
      (∀ q : ℕ, q.Prime → ¬q ∣ N * ell →
        ∀ A : ValuationSubring Qbar, (q : Qbar) ∈ A.nonunits →
          ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
            σ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype →
              ρ σ = 1 ∧ ρint σ = 1 ∧ ρres σ = 1) ∧
      ∀ q : ℕ, q.Prime → ¬q ∣ N * ell →
        ∀ A : ValuationSubring Qbar, (q : Qbar) ∈ A.nonunits →
          ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
            (∃ hd : σ ∈ A.decompositionSubgroup ℚ,
              ∀ z : IsLocalRing.ResidueField A,
                (⟨σ, hd⟩ : A.decompositionSubgroup ℚ) • z = z ^ q) →
            let a : 𝒪[E] := ⟨τ (sourcePrimitiveFieldCoefficient f q),
              by exact sourcePrimitiveCoefficient_valuation_le_one (F := E) f (by norm_num) τ q⟩
            (ρint σ).val.charpoly = X ^ 2 - C a * X + C (q : 𝒪[E]) ∧
            (ρres σ).val.charpoly = X ^ 2 - C (IsLocalRing.residue 𝒪[E] a) * X + C (q : 𝓀[E]) ∧
            (ρres σ).val.trace = IsLocalRing.residue 𝒪[E] a ∧ (ρres σ).val.det = (q : 𝓀[E]) := by
  have hsrc := originalPrimitive_prescribed_continuous_galois_realization N ell f τ.toRingHom
  rcases hsrc with ⟨π, ρ, hc, hs, hH, hact⟩
  letI : Module.Finite ℤ_[ell] (TateModule ell (originalJZero N)) :=
    (original_tate_free_finite_rank N ell).2.1
  have hlattice := padicSpecialization_stable_lattice ell E π hs (originalTateGaloisRep N ell) ρ hact
  rcases hlattice with ⟨L, _, hspan, hfree, hfinite, hrank, hstable⟩
  have hresidual := stableLattice_integral_residual_realization ρ hc L hspan hfree hfinite hrank hstable
  rcases hresidual with ⟨e, ρint, ρres, hci, hcr, hres, hfield⟩
  refine ⟨(localCoefficientResidue_finite_discrete E).1,
    (localCoefficientResidue_finite_discrete E).2, padicCoefficientResidue_charP ell E,
    π, ρ, e, ρint, ρres, hc, hs, hH, hact, hci, hcr, hres, hfield, ?_, ?_⟩
  · intro q hq hNq A hA σ hσ
    exact original_residual_inertia_identity N ell π ρ hs hact e ρint ρres hres hfield
      A q hq hNq hA σ hσ
  · intro q hq hNq A hA σ hσ
    exact original_residual_frobenius_charpoly N ell f τ π ρ hs
      (fun r x => hH r x) hact e ρint ρres hres hfield A q hq hNq hA σ hσ

end
end Dubon2026.SourceFunctionField.OriginalChart
