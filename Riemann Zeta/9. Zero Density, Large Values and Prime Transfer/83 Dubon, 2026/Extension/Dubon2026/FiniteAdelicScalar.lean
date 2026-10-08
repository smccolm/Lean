import Dubon2026.AdelicRealScalar

/-! # The actual trivial finite-idele scalar character of the original cusp function -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix UpperHalfPlane CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- Every actual everywhere-integral idele unit supplies a genuine scalar in the finite level group. -/
theorem finiteAdele_integral_unit_scalar_mem (N : ℕ) (u : finiteAdeleIntegerSubringˣ) :
    GeneralLinearGroup.scalar (Fin 2)
      (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u) ∈ finiteAdeleGL2Gamma0 N := by
  have hs (v : finiteAdeleIntegerSubringˣ) : finiteAdeleLevelMatrix N
      (GeneralLinearGroup.scalar (Fin 2)
        (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom v)).val := by
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.scalar, Matrix.scalar]
    · exact ⟨0, finiteAdeleIntegerSubring.zero_mem, by simp [GeneralLinearGroup.scalar, Matrix.scalar]⟩
  constructor
  · exact hs u
  · rw [← map_inv, ← map_inv]
    exact hs u⁻¹

/-- The original full adelic cusp function has trivial character under every actual finite-idele scalar. -/
theorem fullAdelicGL2CuspLift_finite_scalar (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (b : (FiniteAdeleRing ℤ ℚ)ˣ)
    (g : GeneralLinearGroup (Fin 2) ℝ) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    fullAdelicGL2CuspLift N k f g (GeneralLinearGroup.scalar (Fin 2) b * a) =
      fullAdelicGL2CuspLift N k f g a := by
  obtain ⟨q, hq, u, hu⟩ := finiteIdele_positive_rational_integral_unit b
  let v : ℚˣ := Units.mk0 q hq.ne'
  let w : (FiniteAdeleRing ℤ ℚ)ˣ := Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u
  let δ : GeneralLinearGroup (Fin 2) ℚ := GeneralLinearGroup.scalar (Fin 2) v
  have hb : b = Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom v * w := by
    apply Units.ext
    exact hu
  have hfinite : rationalGL2ToFinite δ =
      GeneralLinearGroup.scalar (Fin 2)
        (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom v) :=
    gl2Scalar_map _ v
  have hr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hreal : rationalGL2ToReal δ = (realPositiveScalar (q : ℝ) hr).val := by
    dsimp only [rationalGL2ToReal, δ]
    rw [gl2Scalar_map]
    apply congrArg (GeneralLinearGroup.scalar (Fin 2))
    apply Units.ext
    rfl
  have hprod : GeneralLinearGroup.scalar (Fin 2) b * a =
      (rationalGL2ToFinite δ * a) * GeneralLinearGroup.scalar (Fin 2) w := by
    rw [hb, map_mul, ← hfinite, mul_assoc, gl2Scalar_mul_comm, ← mul_assoc]
  rw [hprod, fullAdelicGL2CuspLift_level_invariant N f g _
    ⟨GeneralLinearGroup.scalar (Fin 2) w, finiteAdele_integral_unit_scalar_mem N u⟩]
  calc
    fullAdelicGL2CuspLift N k f g (rationalGL2ToFinite δ * a) =
        fullAdelicGL2CuspLift N k f (rationalGL2ToReal δ * g) (rationalGL2ToFinite δ * a) := by
      rw [hreal, fullAdelicGL2CuspLift_real_scalar]
    _ = fullAdelicGL2CuspLift N k f g a :=
      fullAdelicGL2CuspLift_rational_invariant N f δ g a

end
end Dubon2026
