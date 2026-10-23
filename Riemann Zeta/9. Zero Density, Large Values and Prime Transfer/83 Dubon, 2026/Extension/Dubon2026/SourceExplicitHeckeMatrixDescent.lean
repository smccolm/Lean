import Dubon2026.SourceHeckeMatrixPadicRankTwo
import Dubon2026.SourceHeckePrimeImageGeneration

/-! Retain the exact generated matrix algebra in the existing rank-two
descent, for the prescribed primitive-character specialization in DUB-17/18.
This is a direct consumer of the already proved rational-generator and
p-adic-coordinate theorems, with their original hypotheses unchanged. -/
namespace Dubon2026.SourceHeckeMatrixDescent
noncomputable section
open Matrix
variable {A : Type} [CommRing A] {n : ℕ}

theorem explicit_descent (M : A →+* Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (hn : 2 * g M = n)
    (hw : ∃ w : Fin 2 → Fin n → ℝ,
      Submodule.span ℝ (Set.range fun ta : A × Fin 2 => MK M ℝ ta.1 *ᵥ w ta.2) = ⊤) :
    ∃ e : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 → Tp M p),
      ∀ (t : A) (v : Fin n → ℚ_[p]),
        e ((M t).map (Int.cast : ℤ → ℚ_[p]) *ᵥ v) = fun i => φ M p t * e v i := by
  obtain ⟨vq, hv⟩ := exists_rat_isUnit_Φ M hn hw
  obtain ⟨e, he⟩ := exists_equiv M p hn vq hv
  refine ⟨e, fun t v => ?_⟩
  simpa only [MK_apply, Pi.smul_apply, smul_eq_mul] using he t v

open scoped IsMulCommutative in
theorem explicit_descent_prime_generators {I : Type} [Algebra ℤ A]
    (M : A →+* Matrix (Fin n) (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (w : FreeAlgebra ℤ I →ₐ[ℤ] A) (hw : Function.Surjective w) :
    Algebra.adjoin ℚ_[p] (Set.range fun i => φ M p (w (FreeAlgebra.ι ℤ i))) = ⊤ := by
  letI := Tp_commutative M p
  exact primeImage_adjoin_eq_top w hw (φ M p) (adjoin_range_φ M p)

end
end Dubon2026.SourceHeckeMatrixDescent
