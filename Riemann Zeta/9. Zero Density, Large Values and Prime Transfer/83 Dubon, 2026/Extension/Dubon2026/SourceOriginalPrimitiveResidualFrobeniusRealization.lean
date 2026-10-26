import Dubon2026.SourceOriginalResidualFrobeniusCharpoly
import Dubon2026.SourceOriginalResidualInertia

/-! DUB-17/18 -> actual residual association. Unpack the existing genuine
primitive residual realization and retain its local coefficient structure,
finite residue field, continuity, original Hecke specialization, integral
basis comparison and entrywise reduction. Derive inertia triviality and
the exact Frobenius polynomials and residual trace/determinant for these
same representations, with no local-compatibility hypotheses supplied. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open scoped ValuativeRel
open Matrix
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]
local notation "Qbar" => AlgebraicClosure ℚ

private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem originalPrimitive_continuous_residual_frobenius_realization (f : PrimitiveCuspForm N 2) :
    letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
    let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[ell]
    letI : ValuativeRel ℚ_[ell] :=
      ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[ell]))
    ∃ (u : UniformSpace E) (_ : ValuativeRel E),
      letI : TopologicalSpace E := u.toTopologicalSpace
      letI : TopologicalSpace 𝓀[E] :=
        inferInstanceAs (TopologicalSpace (𝒪[E] ⧸ IsLocalRing.maximalIdeal 𝒪[E]))
      IsUniformAddGroup E ∧ IsNonarchimedeanLocalField E ∧ IsModuleTopology ℚ_[ell] E ∧
      (ValuativeRel.valuation ℚ_[ell]).HasExtension (ValuativeRel.valuation E) ∧
      Finite 𝓀[E] ∧ DiscreteTopology 𝓀[E] ∧ CharP 𝓀[E] ell ∧
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
        (π : originalRationalTateModule N ell →ₗ[ℚ_[ell]] (Fin 2 → E))
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
              (ρint σ).val.charpoly = (Polynomial.X : Polynomial 𝒪[E]) ^ 2 - Polynomial.C (R := 𝒪[E]) a * (Polynomial.X : Polynomial 𝒪[E]) +
                Polynomial.C (R := 𝒪[E]) (q : 𝒪[E]) ∧
              (ρres σ).val.charpoly = (Polynomial.X : Polynomial 𝓀[E]) ^ 2 -
                Polynomial.C (R := 𝓀[E]) (IsLocalRing.residue 𝒪[E] a) * (Polynomial.X : Polynomial 𝓀[E]) + Polynomial.C (R := 𝓀[E]) (q : 𝓀[E]) ∧
              (ρres σ).val.trace = IsLocalRing.residue 𝒪[E] a ∧
              (ρres σ).val.det = (q : 𝓀[E]) := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  have hsrc := originalPrimitive_continuous_residual_realization N ell f
  rcases hsrc with ⟨u, v, hu, hl, hm, hv, hfin, hdisc, hchar,
    τ, π, ρ, e, ρint, ρres, hc, hs, hH, hact, hci, hcr, hres, hfield⟩
  let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[ell]
  letI : UniformSpace E := u
  letI : TopologicalSpace E := u.toTopologicalSpace
  letI : ValuativeRel E := v
  refine ⟨u, v, hu, hl, hm, hv, hfin, hdisc, hchar,
    τ, π, ρ, e, ρint, ρres, hc, hs, hH, hact, hci, hcr, hres, hfield, ?_, ?_⟩
  · intro q hq hNq A hA σ hσ
    exact original_residual_inertia_identity N ell π ρ hs hact e ρint ρres hres hfield
      A q hq hNq hA σ hσ
  · intro q hq hNq A hA σ hσ
    exact original_residual_frobenius_charpoly N ell f τ π ρ hs
      (fun r x => hH r x) hact e ρint ρres hres hfield A q hq hNq hA σ hσ

end
end Dubon2026.SourceFunctionField.OriginalChart
