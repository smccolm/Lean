import Dubon2026.SymmetricResidualRootLifts
import Dubon2026.FiniteSymmetricRegularDiagonal

/-! Scalar witnesses for the actual two-dimensional residual image and
its symmetric powers. DUB-17 uses these to detect twisted dual classes
on a root-fixing kernel by the central-scalar cocycle argument. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- The original symmetric matrix of a scalar is the exact degree-power
scalar over the coefficient ring. -/
theorem homogeneousSymmetricGL_scalar_ring {R : Type*} [CommRing R]
    (n : ℕ) (u : Rˣ) :
    homogeneousSymmetricGL n (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin (n + 1)) (u ^ n) := by
  apply Units.ext
  rw [homogeneousSymmetricGL_val]
  change LinearMap.toMatrix (binaryHomogeneousMonomialBasis n)
    (binaryHomogeneousMonomialBasis n)
    (homogeneousMatrixAction n (GeneralLinearGroup.scalar (Fin 2) u).val) = _
  have hs : (GeneralLinearGroup.scalar (Fin 2) u).val =
      Matrix.diagonal ![(u : R), (u : R)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hs, homogeneousDiagonal_toMatrix_ring]
  change Matrix.diagonal (fun i : Fin (n + 1) =>
      (u : R) ^ i.val * (u : R) ^ (n - i.val)) =
    Matrix.diagonal (fun _ => ((u ^ n : Rˣ) : R))
  congr 1
  funext i
  rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt), Units.val_pow_eq_pow_val]

/-- Full SL2 image supplies a scalar element with the square of any
prescribed character value, by a lift in the character kernel. -/
theorem residualGL2_exists_scalar_character_square
    {G B K : Type} [Group G] [CommGroup B] [Field K]
    [NeZero (2 : K)] [NeZero (3 : K)]
    (ρ : G →* GeneralLinearGroup (Fin 2) K) (χ : G →* B)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := K)).range ≤ ρ.range)
    (g : G) :
    ∃ σ : G, χ σ = χ g ^ 2 ∧
      ρ σ = GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det (ρ g)) := by
  let b := GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det (ρ g)) *
    (ρ g ^ 2)⁻¹
  have hb : GeneralLinearGroup.det b = 1 := by
    simp [b, map_mul, map_inv, map_pow, GeneralLinearGroup.det_scalar]
  let s : SL(2, K) := ⟨b.val, congrArg Units.val hb⟩
  have hs : SpecialLinearGroup.toGL s = b := Units.ext rfl
  letI : Group.IsPerfect SL(2, K) := fieldSL2_isPerfect
  letI : Group.IsPerfect (SpecialLinearGroup.toGL (n := Fin 2) (R := K)).range :=
    Group.IsPerfect.range SpecialLinearGroup.toGL
  have hk := perfect_subgroup_le_map_character_kernel ρ χ
    (SpecialLinearGroup.toGL (n := Fin 2) (R := K)).range himage
  obtain ⟨τ, hτ, heτ⟩ := Subgroup.mem_map.mp
    (hk (show SpecialLinearGroup.toGL s ∈
      (SpecialLinearGroup.toGL (n := Fin 2) (R := K)).range from ⟨s, rfl⟩))
  refine ⟨τ * g ^ 2, ?_, ?_⟩
  · change χ τ = 1 at hτ
    rw [map_mul, hτ, one_mul, map_pow]
  · rw [map_mul, map_pow, heτ, hs]
    exact inv_mul_cancel_right _ _

/-- Scalar matrices commute with every original matrix in the same GL. -/
theorem generalLinear_scalar_commute {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing K] (u : Kˣ) (g : GeneralLinearGroup ι K) :
    Commute (GeneralLinearGroup.scalar ι u) g := by
  apply Units.ext
  change Matrix.scalar ι (u : K) * g.val = g.val * Matrix.scalar ι (u : K)
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

end
end Dubon2026
