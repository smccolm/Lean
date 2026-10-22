import Dubon2026.SourceOriginalLoopPeriodInjectivity
import Dubon2026.SourceOriginalPathIntegralLinearCombination

/-! DUB-17/18 -> original torsion cardinality -> Abel converse -> period correction.
The exact regular-period generation and raw bilinear/third-kind reciprocity
clauses give an original regular differential whose subtraction leaves integer
2 pi i periods on the 2g generating loops. Geometric reciprocity and generation
remain explicit upstream inputs; no symplectic basis or period-matrix
injectivity is supplied. Extension to all avoiding loops remains downstream.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set KaehlerDifferential Matrix
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

private theorem raw_pairing_eq {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (y : Fin n ⊕ Fin n → ℂ) (i : Fin n) :
    (A.transpose * Q.map (Int.castRingHom ℂ)).mulVec y i =
      ∑ k, ∑ l, (Q k l : ℂ) * A k i * y l := by
  simp only [Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change A k i * (Q k l : ℂ) * y l = _
  ring

theorem exists_original_generator_period_correction {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    (P₀ : Place ℂ F) (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hD : abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈
      pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])))
    (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) (hQ : IsUnit Q.det)
    (hgen : ∀ (P : Place ℂ F) (γ : Path P P), ∃ κ : Fin n ⊕ Fin n → ℤ,
      ∀ i, pathIntegral N (b i : Ω[F⁄ℂ]) γ =
        ∑ k, (κ k : ℂ) * pathIntegral N (b i : Ω[F⁄ℂ]) (Z k))
    (hRR : ∀ i j : Fin n, ∑ k, ∑ l, (Q k l : ℂ) *
      pathIntegral N (b i : Ω[F⁄ℂ]) (Z k) * pathIntegral N (b j : Ω[F⁄ℂ]) (Z l) = 0)
    (hrec : ∃ κ : Fin n ⊕ Fin n → ℤ, ∀ i : Fin n,
      ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral N (b i : Ω[F⁄ℂ]) (Z k) *
        pathIntegral N η (Z l) = 2 * Real.pi * Complex.I *
          (abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ D i +
            ∑ k, (κ k : ℂ) * pathIntegral N (b i : Ω[F⁄ℂ]) (Z k))) :
    ∃ ζ ∈ regularDifferentials ℂ F, ∃ m : Fin n ⊕ Fin n → ℤ,
      ∀ k, pathIntegral N η (Z k) - pathIntegral N ζ (Z k) =
        2 * Real.pi * Complex.I * (m k : ℂ) := by
  classical
  let A : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ := fun k i =>
    pathIntegral N (b i : Ω[F⁄ℂ]) (Z k)
  have hAm : Function.Injective A.mulVecLin :=
    original_loop_period_matrix_injective N b Pz Z hgen
  have hRm : (A.transpose * Q.map (Int.castRingHom ℂ)) * A = 0 := by
    ext i j
    change (A.transpose * Q.map (Int.castRingHom ℂ)).mulVec (fun l => A l j) i = 0
    rw [raw_pairing_eq]
    exact hRR i j
  obtain ⟨μ, hμ⟩ := exists_original_period_coordinates N (fun i => (b i : Ω[F⁄ℂ])) Pz Z hgen hD
  obtain ⟨κ, hκ⟩ := hrec
  have hrecM : (A.transpose * Q.map (Int.castRingHom ℂ)).mulVec
      (fun k => pathIntegral N η (Z k)) =
        (2 * Real.pi * Complex.I) • A.transpose.mulVec (fun k => ((μ k + κ k : ℤ) : ℂ)) := by
    ext i
    rw [raw_pairing_eq, hκ i, hμ]
    simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Pi.smul_apply,
      smul_eq_mul, Int.cast_add, A]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  obtain ⟨c, m, hm⟩ := PeriodCorrection.exists_integer_period_correction A Q hAm hQ hRm
    (fun k => pathIntegral N η (Z k)) (2 * Real.pi * Complex.I) (fun k => μ k + κ k) hrecM
  refine ⟨∑ i, c i • (b i : Ω[F⁄ℂ]),
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (b i).2), m, ?_⟩
  intro k
  rw [pathIntegral_sum_smul N c (fun i => (b i : Ω[F⁄ℂ])) (fun i => (b i).2)]
  simpa only [Matrix.mulVec, dotProduct, A, mul_comm] using hm k

end
end Dubon2026.SourceFunctionField.OriginalChart
