import Dubon2026.SourceCyclotomicModularLift

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> preservation of the original Gamma1 level under cyclotomic
conjugation. The conjugate of a Gamma1 torsion action is lifted by an
explicit integral translation, retaining the actual level condition. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Matrix UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups Manifold ModularForm

theorem exists_gammaOne_cyclotomic_conjugate (N : ℕ) [NeZero N] (s : ℕ) (hs : s.Coprime N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    ∃ γ' ∈ Gamma1 N, ∀ v : Fin 2 → ZMod N,
      vecMulSL N (cyclotomicTorsionVector s v) γ =
        cyclotomicTorsionVector s (vecMulSL N v γ') := by
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime s hs
  let t : ℤ := (((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)
  have hst : (s : ZMod N) * (t : ZMod N) = 1 := by
    have h1 : (u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := Units.mul_inv u
    simpa only [t, Int.cast_natCast, ZMod.natCast_zmod_val] using h1
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem N γ).mp hγ
  refine ⟨ModularGroup.T ^ ((γ 0 1 : ℤ) * t),
    (Gamma1 N).zpow_mem (by simp [Gamma1_mem, ModularGroup.T]) _, fun v => ?_⟩
  have hT : ((ModularGroup.T ^ ((γ 0 1 : ℤ) * t) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
      ((↑) : ℤ → ZMod N) = !![1, ((γ 0 1 : ℤ) : ZMod N) * t; 0, 1] := by
    rw [ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hγm : (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) =
      !![1, ((γ 0 1 : ℤ) : ZMod N); 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h10]
  funext i
  simp only [vecMulSL, hT, hγm, cyclotomicTorsionVector]
  fin_cases i
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    linear_combination (-(v 0 * ((γ 0 1 : ℤ) : ZMod N))) * hst

end
end Dubon2026.SourceFricke
