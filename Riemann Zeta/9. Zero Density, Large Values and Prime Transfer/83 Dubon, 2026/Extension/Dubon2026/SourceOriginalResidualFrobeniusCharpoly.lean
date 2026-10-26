import Dubon2026.SourceOriginalSpecializationFrobeniusCharpoly
import Dubon2026.SourceIntegralMatrixCharpoly
import Dubon2026.SourceRankTwoCharpolyCoefficients
import Dubon2026.SourceOriginalPrimitiveResidualRealization

/-! DUB-17/18 -> actual residual association. The original Fourier
coefficient is integral by the already proved coefficient theorem.
The existing lattice comparison and literal entrywise residue map carry
the original Frobenius polynomial to the same residual representation. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open scoped ValuativeRel
open SourceCurve Matrix Polynomial
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]
variable {E : Type} [Field E] [Algebra ℚ_[ell] E]
variable [CharZero E] [ValuativeRel E]
private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem original_residual_frobenius_charpoly
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (π : originalRationalTateModule N ell →ₗ[ℚ_[ell]] (Fin 2 → E))
    (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
    (hspan : Submodule.span E (Set.range π) = ⊤)
    (hH : ∀ (q : Nat.Primes) (x : originalRationalTateModule N ell),
      π ((TateModule.tateMap ell (originalHeckePicard Qbar N q.val)).baseChange ℚ_[ell] x) =
        τ (sourcePrimitiveFieldCoefficient f q.val) • π x)
    (hact : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N ell),
      (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N ell σ x))
    (e : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E))
    (ρint : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) 𝒪[E])
    (ρres : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) 𝓀[E])
    (hres : ∀ σ i j, (ρres σ).val i j = IsLocalRing.residue 𝒪[E] ((ρint σ).val i j))
    (hfield : ∀ σ v, (ρint σ).val.map (algebraMap 𝒪[E] E) *ᵥ e v = e ((ρ σ).val *ᵥ v))
    (A : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hNp : ¬p ∣ N * ell)
    (hA : (p : Qbar) ∈ A.nonunits) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (hσ : ∃ hd : σ ∈ A.decompositionSubgroup ℚ,
      ∀ a : IsLocalRing.ResidueField A,
        (⟨σ, hd⟩ : A.decompositionSubgroup ℚ) • a = a ^ p) :
    let a : 𝒪[E] := ⟨τ (sourcePrimitiveFieldCoefficient f p),
      by exact sourcePrimitiveCoefficient_valuation_le_one (F := E) f (by norm_num) τ p⟩
    (ρint σ).val.charpoly = X ^ 2 - C a * X + C (p : 𝒪[E]) ∧
    (ρres σ).val.charpoly = X ^ 2 - C (IsLocalRing.residue 𝒪[E] a) * X + C (p : 𝓀[E]) ∧
    (ρres σ).val.trace = IsLocalRing.residue 𝒪[E] a ∧
    (ρres σ).val.det = (p : 𝓀[E]) := by
  let a : 𝒪[E] := ⟨τ (sourcePrimitiveFieldCoefficient f p),
    by exact sourcePrimitiveCoefficient_valuation_le_one (F := E) f (by norm_num) τ p⟩
  have hf := (original_specialization_frobenius_charpoly N ell f τ.toRingHom π ρ
    hspan hH hact A p hp hNp hA σ hσ).2.2
  have hp' : (ρ σ).val.charpoly =
      (X ^ 2 - C a * X + C (p : 𝒪[E])).map (algebraMap 𝒪[E] E) := by
    simpa only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_natCast, map_natCast] using hf
  have h := residue_matrix_charpoly_of_intertwiner (algebraMap 𝒪[E] E)
    Subtype.val_injective (IsLocalRing.residue 𝒪[E]) (ρint σ).val (ρ σ).val (ρres σ).val
    e (hfield σ) (hres σ) _ hp'
  have hr : (ρres σ).val.charpoly =
      X ^ 2 - C (IsLocalRing.residue 𝒪[E] a) * X + C (p : 𝓀[E]) := by
    simpa only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_natCast, map_natCast] using h.2
  exact ⟨h.1, hr, rank_two_trace_det_of_charpoly (ρres σ).val _ _ hr⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
