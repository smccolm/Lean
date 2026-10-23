import Dubon2026.SourceOriginalRationalTateRankTwo
import Dubon2026.SourceHeckePrimeImageGeneration

/-! DUB-17/18 -> actual modular residual association -> original rational
Tate rank-two Hecke realization. Construct the original bases and base
point from their proved existence, and retain the literal arithmetic
Picard correspondences at every prime, including primes dividing the level.
Frobenius and inertia compatibility are separate remaining obligations. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalRationalTateHeckeWord_prime (ell : Nat.Primes) :
    originalRationalTateHeckeWord N p (FreeAlgebra.ι ℤ ell) =
      (TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val)).baseChange
        ℚ_[p] := by
  exact congrArg (fun u : Module.End ℤ_[p] (TateModule p (originalJZero N)) =>
    u.baseChange ℚ_[p]) (originalTateHeckeWord_generator N p ell)

private theorem originalRationalTate_prime_rankTwo_of_basis {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra ℚ_[p] T)
      (χ : Nat.Primes → T)
      (e : originalRationalTateModule N p ≃ₗ[ℚ_[p]] (Fin 2 → T)),
      Algebra.adjoin ℚ_[p] (Set.range χ) = ⊤ ∧
      ∀ (ell : Nat.Primes) (x : originalRationalTateModule N p),
        e ((TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val)).baseChange
          ℚ_[p] x) = χ ell • e x := by
  obtain ⟨T, hT, hA, φ, e, hgen, hact⟩ := originalRationalTate_heckeWord_rankTwo N p b P₀ lb
  let χ : Nat.Primes → T := fun ell => φ (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell))
  refine ⟨T, hT, hA, χ, e, ?_, ?_⟩
  · with_reducible
      exact primeImage_adjoin_eq_top (K := ℚ_[p])
        (A := originalFullLatticeHeckeAlgebra N b) (T := T)
        (originalFullLatticeHeckeWord N b) (originalFullLatticeHeckeWord_surjective N b) φ hgen
  · intro ell x
    exact (congrArg (fun u : Module.End ℚ_[p] (originalRationalTateModule N p) => e (u x))
      (originalRationalTateHeckeWord_prime N p ell)).symm.trans (hact (FreeAlgebra.ι ℤ ell) x)

theorem originalRationalTate_prime_rankTwo :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra ℚ_[p] T)
      (χ : Nat.Primes → T)
      (e : originalRationalTateModule N p ≃ₗ[ℚ_[p]] (Fin 2 → T)),
      Algebra.adjoin ℚ_[p] (Set.range χ) = ⊤ ∧
      ∀ (ell : Nat.Primes) (x : originalRationalTateModule N p),
        e ((TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val)).baseChange
          ℚ_[p] x) = χ ell • e x := by
  letI := finite_original_regularDifferentials N ℂ
  let b := Module.finBasis ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
  obtain ⟨P₀⟩ := nonempty_original_places N ℂ
  exact originalRationalTate_prime_rankTwo_of_basis N p b P₀ (originalPeriodLatticeBasis N b)

end
end Dubon2026.SourceFunctionField.OriginalChart
