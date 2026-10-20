import Dubon2026.FiniteBaseCMSymmetricTangent
import Dubon2026.FiniteBaseCMSymmetricIrreducible
import Dubon2026.PolarizedAdjointScalarSign
import Dubon2026.MatrixAdjointScalarDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The original polarized symmetric-power full adjoint has no invariants.
Actual CM absolute irreducibility makes an invariant matrix scalar; the
original real-place component negates that scalar. This discharges the H0
term in the source polarized Selmer comparison required by DUB-17. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the full-adjoint invariant consumer. -/
local instance finiteBaseCMSymmetricAdjointUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  {L : Type} [Field L] [Finite L] [TopologicalSpace L] [DiscreteTopology L]
  (q n : ℕ) [Fact q.Prime] [CharP L q] (hn : n < q)
  (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) L)
  (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1)

/-- The actual polarized full-adjoint invariant matrix vanishes from the original full SL2 image and source bounds. -/
theorem finiteBaseCMSymmetricAdjointInvariant_eq_zero
    (hq : 3 < q) (hsize : 2 * n < Nat.card L - 1)
    (himage : (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := L)).range ≤ ρ.toMonoidHom.range)
    (X : Representation.invariants (polarizedAdjointRepresentation.comp
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
        (factorial_cast_ne_zero_of_lt_char q n hn) hodd).toMonoidHom)) :
    X.val = 0 := by
  let r := (MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a F K n ρ).toMonoidHom
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure L) r)) :=
    finiteBaseCMSymmetricMatrices_absoluteIrreducible a F K q n ρ himage hq hsize hn
  let Y : (matrixAdjointRepresentation r).invariants := ⟨X.val, by
    intro g
    have hx := X.property g.val
    change polarizedAdjointRepresentation
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
        (factorial_cast_ne_zero_of_lt_char q n hn) hodd g.val) X.val = X.val at hx
    rw [finiteBaseCMSymmetricPolarizedRepresentation_kernel,
      polarizedAdjointRepresentation_identity] at hx
    change (r g).val * X.val * (r g⁻¹).val = X.val
    rw [map_inv]
    exact hx⟩
  obtain ⟨d, hd⟩ := matrixAdjointInvariant_eq_scalar_of_extension
    (L := AlgebraicClosure L) r Y
  change X.val = d • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) at hd
  have hc := finiteBaseCMSymmetricPolarizedRepresentation_component a F K n ρ
    (factorial_cast_ne_zero_of_lt_char q n hn) hodd (finiteBaseRealConjugation a F)
  rw [finiteBaseCMComponent_conjugation] at hc
  have hx := X.property (finiteBaseRealConjugation a F)
  change polarizedAdjointRepresentation
    (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
      (factorial_cast_ne_zero_of_lt_char q n hn) hodd (finiteBaseRealConjugation a F)) X.val = X.val at hx
  rw [hd, polarizedAdjoint_scalar_nonidentity _ hc] at hx
  have hii := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) L => M 0 0) hx
  simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hii
  have htwo : (2 : L) * d = 0 := by linear_combination -hii
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) ((CharP.cast_eq_zero_iff L q 2).mp h)
    omega
  have hd0 : d = 0 := (mul_eq_zero.mp htwo).resolve_left h2
  simpa only [hd0, zero_smul] using hd

/-- The source full-adjoint invariant submodule for the actual CM symmetric power is zero. -/
theorem finiteBaseCMSymmetricAdjoint_invariants_eq_bot
    (hq : 3 < q) (hsize : 2 * n < Nat.card L - 1)
    (himage : (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := L)).range ≤ ρ.toMonoidHom.range) :
    Representation.invariants (polarizedAdjointRepresentation.comp
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ
        (factorial_cast_ne_zero_of_lt_char q n hn) hodd).toMonoidHom) = ⊥ := by
  apply bot_unique
  intro X hX
  change X = 0
  exact finiteBaseCMSymmetricAdjointInvariant_eq_zero a F K q n hn ρ hodd hq hsize himage ⟨X, hX⟩

end
end Dubon2026
