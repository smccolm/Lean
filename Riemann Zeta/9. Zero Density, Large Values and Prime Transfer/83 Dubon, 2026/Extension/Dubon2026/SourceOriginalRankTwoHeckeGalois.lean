import Dubon2026.SourceOriginalRationalTatePrimeRankTwo
import Dubon2026.SourceOriginalRationalTateGalois
import Dubon2026.SourceHeckeLinearGaloisTransport

/-! DUB-17/18 -> modular residual association -> actual original rank-two
Hecke Galois action. The coefficient algebra and rank-two equivalence are
constructed by the preceding original Tate theorem. Actual Picard Galois
commutation proves linearity over that algebra. This retains the literal
arithmetic action; continuity, Frobenius/inertia and eigenvalue factors
remain separate obligations. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "Qbar" => AlgebraicClosure ℚ

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalRationalTate_rankTwo_hecke_galois :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra ℚ_[p] T)
      (χ : Nat.Primes → T)
      (e : originalRationalTateModule N p ≃ₗ[ℚ_[p]] (Fin 2 → T))
      (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* Module.End T (Fin 2 → T)),
      Algebra.adjoin ℚ_[p] (Set.range χ) = ⊤ ∧
      (∀ (ell : Nat.Primes) (x : originalRationalTateModule N p),
        e ((TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange
          ℚ_[p] x) = χ ell • e x) ∧
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N p),
        ρ σ (e x) = e (originalRationalTateGaloisRep N p σ x) := by
  obtain ⟨T, hT, hA, χ, e, hgen, hact⟩ := originalRationalTate_prime_rankTwo N p
  let u : Nat.Primes → Module.End ℚ_[p] (originalRationalTateModule N p) := fun ell =>
    (TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange ℚ_[p]
  let ρ := heckeLinearGaloisRep χ hgen u e hact (originalRationalTateGaloisRep N p)
    (originalRationalTateGaloisRep_prime_commute N p)
  refine ⟨T, hT, hA, χ, e, ρ, hgen, hact, ?_⟩
  exact heckeLinearGaloisRep_equivariant χ hgen u e hact (originalRationalTateGaloisRep N p)
    (originalRationalTateGaloisRep_prime_commute N p)

end
end Dubon2026.SourceFunctionField.OriginalChart
