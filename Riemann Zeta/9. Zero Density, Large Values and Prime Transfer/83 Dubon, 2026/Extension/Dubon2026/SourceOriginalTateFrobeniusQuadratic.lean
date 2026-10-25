import Dubon2026.SourceOriginalPicardFrobeniusQuadratic
import Dubon2026.SourceOriginalTateInertia

/-! DUB-17/18 -> original primitive weight-two Frobenius polynomial.
Every actual Tate coordinate lies in residue-invertible prime-power Picard
torsion, so the original Picard quadratic identity applies coordinatewise.
The existing endomorphism base-change ring homomorphism then gives exactly
the same identity on rational Tate space. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve

private theorem endomorphism_baseChange_quadratic
    (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (H G : Module.End R M) (p : ℕ)
    (h : H * G = G * G + p • 1) :
    H.baseChange S * G.baseChange S =
      G.baseChange S * G.baseChange S + p • 1 := by
  let φ := (Module.End.baseChangeHom R S M).toRingHom
  have hh := congrArg φ h
  simpa only [map_mul, map_add, map_nsmul, map_one] using hh

local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N p : ℕ) [NeZero N] [Fact p.Prime]
variable [CharP (IsLocalRing.ResidueField A) p]
local notation "kk" => IsLocalRing.ResidueField A

theorem originalTateGaloisRep_frobenius_quadratic
    (hpN : ¬ p ∣ N) (hNk : (N : kk) ≠ 0)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : kk) ≠ 0)
    (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : ∃ hd : τ ∈ A.decompositionSubgroup ℚ,
      ∀ a : kk, (⟨τ, hd⟩ : A.decompositionSubgroup ℚ) • a = a ^ p) :
    TateModule.tateMap ell (originalHeckePicard Qbar N p) * originalTateGaloisRep N ell τ =
      originalTateGaloisRep N ell τ * originalTateGaloisRep N ell τ + p • 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change originalHeckePicard Qbar N p
      (originalArithmeticPicard N τ ((x : ℕ → originalJZero N) n)) =
    originalArithmeticPicard N τ
      (originalArithmeticPicard N τ ((x : ℕ → originalJZero N) n)) +
        p • ((x : ℕ → originalJZero N) n)
  apply originalArithmeticPicard_frobenius_quadratic A N p hpN hNk τ hτ
    (ell ^ n) (by simpa only [Nat.cast_pow] using pow_ne_zero n hell)
  exact Pic0.mem_torsion_iff.mp (originalTateTorsionCoordinate N ell n x).property

theorem originalRationalTateGaloisRep_frobenius_quadratic
    (hpN : ¬ p ∣ N) (hNk : (N : kk) ≠ 0)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : kk) ≠ 0)
    (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : ∃ hd : τ ∈ A.decompositionSubgroup ℚ,
      ∀ a : kk, (⟨τ, hd⟩ : A.decompositionSubgroup ℚ) • a = a ^ p) :
    (TateModule.tateMap ell (originalHeckePicard Qbar N p)).baseChange ℚ_[ell] *
        OriginalChart.originalRationalTateGaloisRep N ell τ =
      OriginalChart.originalRationalTateGaloisRep N ell τ *
        OriginalChart.originalRationalTateGaloisRep N ell τ + p • 1 := by
  exact endomorphism_baseChange_quadratic ℤ_[ell] ℚ_[ell]
    (TateModule ell (originalJZero N)) _ _ p
    (originalTateGaloisRep_frobenius_quadratic A N p hpN hNk ell hell τ hτ)

omit [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] in
theorem originalRationalTateGaloisRep_frobenius_quadratic_away
    (hp : p.Prime) (ell : ℕ) [Fact ell.Prime] (hNp : ¬ p ∣ N * ell)
    (hA : (p : Qbar) ∈ A.nonunits) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : ∃ hd : τ ∈ A.decompositionSubgroup ℚ,
      ∀ a : kk, (⟨τ, hd⟩ : A.decompositionSubgroup ℚ) • a = a ^ p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (TateModule.tateMap ell (originalHeckePicard Qbar N p)).baseChange ℚ_[ell] *
        OriginalChart.originalRationalTateGaloisRep N ell τ =
      OriginalChart.originalRationalTateGaloisRep N ell τ *
        OriginalChart.originalRationalTateGaloisRep N ell τ + p • 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI := residue_charP_of_prime_mem_nonunits A p hp hA
  have hpN : ¬ p ∣ N := fun h => hNp (dvd_mul_of_dvd_left h ell)
  have hN : (N : kk) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ p]
    exact hpN
  have hell : (ell : kk) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ p]
    exact fun h => hNp (dvd_mul_of_dvd_right h N)
  exact originalRationalTateGaloisRep_frobenius_quadratic A N p hpN hN ell hell τ hτ

end
end Dubon2026.SourceFunctionField.GaussReduction
