import Dubon2026.SourceOriginalRationalTatePrimeRankTwo
import Dubon2026.SourceExplicitHeckeMatrixDescent
import Dubon2026.SourceExplicitRankTwoCoordinates

/-! DUB-17/18 -> prescribed coefficient specialization -> retain the
literal generated matrix algebra in the original rank-two Tate theorem.
The existing determinant descent and actual Tate coordinate comparison
are reused verbatim as proved inputs; no new descent is performed. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Matrix
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b
private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

open scoped IsMulCommutative

theorem originalFullHecke_explicit_matrix_rankTwo {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    ∃ e : (Fin m → ℚ_[p]) ≃ₗ[ℚ_[p]]
        (Fin 2 → SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p),
      ∀ (t : originalFullLatticeHeckeAlgebra N b) (v : Fin m → ℚ_[p]),
        e ((originalLatticeHeckeMatrix N b lb t).map (Int.cast : ℤ → ℚ_[p]) *ᵥ v) =
          (fun i => SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p t * e v i) := by
  exact SourceHeckeMatrixDescent.explicit_descent (originalLatticeHeckeMatrix N b lb) p
    (originalFullHecke_matrix_rank_twice N b lb)
    (originalFullHecke_real_matrix_two_generators N b lb)

theorem originalRationalTate_explicit_word_rankTwo {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    ∃ e : originalRationalTateModule N p ≃ₗ[ℚ_[p]]
        (Fin 2 → SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p),
      ∀ (a : FreeAlgebra ℤ Nat.Primes) (x : originalRationalTateModule N p),
        e (originalRationalTateHeckeWord N p a x) =
          (fun i => SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
            (originalFullLatticeHeckeWord N b a) * e x i) := by
  exact explicitRankTwo_transfer_coordinates
    (fun t => (originalLatticeHeckeMatrix N b lb t).map (Int.cast : ℤ → ℚ_[p]))
    (originalFullLatticeHeckeWord N b) (originalRationalTateHeckeWord N p)
    (SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p)
    (originalRationalTateBasis N p b P₀ lb).equivFun
    (originalRationalTateBasis_word_coordinates N p b P₀ lb)
    (originalFullHecke_explicit_matrix_rankTwo N p b lb)

theorem originalRationalTate_explicit_prime_rankTwo {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    let T := SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p
    let χ := fun ell : Nat.Primes =>
      SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
        (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell))
    Algebra.adjoin ℚ_[p] (Set.range χ) = ⊤ ∧
      ∃ e : originalRationalTateModule N p ≃ₗ[ℚ_[p]] (Fin 2 → T),
        ∀ (ell : Nat.Primes) (x : originalRationalTateModule N p),
          e ((TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val)).baseChange
            ℚ_[p] x) = (fun i => χ ell * e x i) := by
  refine ⟨?_, ?_⟩
  · have h := SourceHeckeMatrixDescent.explicit_descent_prime_generators
      (originalLatticeHeckeMatrix N b lb) p (originalFullLatticeHeckeWord N b)
      (originalFullLatticeHeckeWord_surjective N b)
    with_reducible exact h
  · exact explicitRankTwo_reindex (originalRationalTateHeckeWord N p)
      (fun ell : Nat.Primes =>
        (TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val)).baseChange ℚ_[p])
      (FreeAlgebra.ι ℤ) (fun ell => (originalRationalTateHeckeWord_prime N p ell).symm)
      (fun a => SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
        (originalFullLatticeHeckeWord N b a))
      (originalRationalTate_explicit_word_rankTwo N p b P₀ lb)

end
end Dubon2026.SourceFunctionField.OriginalChart
