import Dubon2026.SourceCyclotomicFrickeIndex
import Dubon2026.SL2Reduction

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> cyclotomic conjugation at every modular cusp. Reuse the
already proved integral SL2 reduction surjectivity. Conjugation by the
cyclotomic diagonal matrix lifts to an actual integral modular matrix.
Adapted from the frozen anthropics/fermats-last-theorem sigma-transport
proof (6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0). -/
namespace Dubon2026.SourceFricke
noncomputable section
open Matrix UpperHalfPlane
open scoped MatrixGroups Manifold ModularForm

/-- The actual torsion-vector permutation of a cyclotomic exponent. -/
def cyclotomicTorsionVector {N : ℕ} (s : ℕ) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N :=
  ![v 0, (s : ZMod N) * v 1]

theorem exists_modular_cyclotomic_conjugate (N : ℕ) [NeZero N] (s : ℕ) (hs : s.Coprime N)
    (A : SL(2, ℤ)) : ∃ A' : SL(2, ℤ), ∀ v : Fin 2 → ZMod N,
      vecMulSL N (cyclotomicTorsionVector s v) A =
        cyclotomicTorsionVector s (vecMulSL N v A') := by
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime s hs
  let tN : ZMod N := ↑u⁻¹
  have hst : (s : ZMod N) * tN = 1 := Units.mul_inv u
  have hts : tN * (s : ZMod N) = 1 := Units.inv_mul u
  let D : Matrix (Fin 2) (Fin 2) (ZMod N) := !![1, 0; 0, (s : ZMod N)]
  let Di : Matrix (Fin 2) (Fin 2) (ZMod N) := !![1, 0; 0, tN]
  let red : Matrix (Fin 2) (Fin 2) (ZMod N) :=
    (A : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N)
  have hDDi : Di * D = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D, Di, Matrix.mul_apply, Fin.sum_univ_two, hts]
  have hds : ∀ v : Fin 2 → ZMod N, cyclotomicTorsionVector s v = Matrix.vecMul v D := by
    intro v
    funext i
    fin_cases i <;> simp [cyclotomicTorsionVector, D, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  let M' := D * red * Di
  have hdetA : red.det = 1 := by
    exact (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) A).property
  have hdet : M'.det = 1 := by
    rw [show M' = D * red * Di from rfl, Matrix.det_mul, Matrix.det_mul, hdetA]
    simp [D, Di, Matrix.det_fin_two, hst]
  obtain ⟨A', hA'⟩ := Dubon2026.SL2Reduction.SL2_reduction_surjective N ⟨M', hdet⟩
  have hred : (A' : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) = M' := by
    exact congrArg (fun y : SL(2, ZMod N) => (y : Matrix (Fin 2) (Fin 2) (ZMod N))) hA'
  refine ⟨A', fun v => ?_⟩
  rw [vecMulSL, vecMulSL, hds, hds, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hred]
  change Matrix.vecMul v (D * red) = Matrix.vecMul v ((D * red * Di) * D)
  rw [Matrix.mul_assoc (D * red) Di D, hDDi, Matrix.mul_one]

end
end Dubon2026.SourceFricke
