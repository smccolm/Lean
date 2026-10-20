import Dubon2026.GeneralLinearIntegralTorsion

/-! Determinant twists of the literal integral induced module.
Multiplication by the actual determinant unit shifts every original weight
by the same integer. This is the source-preserving reduction of arbitrary
integral weights to nonnegative weights in the finite-generation proof.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

/-- The determinant of the actual generic invertible matrix is the original regular determinant unit. -/
def generalLinearRegularDeterminantUnit : (GeneralLinearRegularFunctions R n)ˣ :=
  GeneralLinearGroup.det (generalLinearRegularGeneric R n)

/-- Evaluating the original regular determinant unit gives the determinant of the same original matrix. -/
theorem generalLinearRegularEval_determinantUnit
    {A : Type u} [CommRing A] [Algebra R A] (g : GeneralLinearGroup (Fin n) A) :
    Units.map (generalLinearRegularEval (R := R) g).toMonoidHom
      generalLinearRegularDeterminantUnit = GeneralLinearGroup.det g := by
  exact (GeneralLinearGroup.map_det (generalLinearRegularEval g).toRingHom
    (generalLinearRegularGeneric R n)).symm.trans
      (congrArg GeneralLinearGroup.det (generalLinearRegularGeneric_eval R n g))

/-- Arbitrary integral powers of the original determinant evaluate as the same determinant power, including negative powers. -/
theorem generalLinearRegularEval_determinant_zpow
    {A : Type u} [CommRing A] [Algebra R A] (g : GeneralLinearGroup (Fin n) A) (c : ℤ) :
    generalLinearRegularEval (R := R) g
      ((generalLinearRegularDeterminantUnit (R := R) (n := n) ^ c :
        (GeneralLinearRegularFunctions R n)ˣ) : GeneralLinearRegularFunctions R n) =
      ((GeneralLinearGroup.det g ^ c : Aˣ) : A) := by
  have h := congrArg (fun z : Aˣ => (z : A))
    (map_zpow (Units.map (generalLinearRegularEval (R := R) g).toMonoidHom)
      generalLinearRegularDeterminantUnit c)
  simpa only [generalLinearRegularEval_determinantUnit, Units.coe_map,
    MonoidHom.coe_coe] using h

/-- The determinant of the original upper Borel matrix equals the product of its actual diagonal units. -/
theorem generalLinearBorel_det (b : generalLinearBorel R n) :
    GeneralLinearGroup.det b.val = ∏ i : Fin n, generalLinearBorelDiagonalUnit b i := by
  apply Units.ext
  simpa only [GeneralLinearGroup.val_det_apply, Units.coe_prod,
    generalLinearBorelDiagonalUnit] using Matrix.det_of_upperTriangular b.property

/-- Shifting every original weight by an integer multiplies the exact Borel character by the corresponding determinant character. -/
theorem generalLinearBorelWeight_shift (lam : Fin n → ℤ) (c : ℤ)
    (b : generalLinearBorel R n) :
    generalLinearBorelWeight (fun i => lam i + c) b =
      generalLinearBorelWeight lam b * GeneralLinearGroup.det b.val ^ c := by
  simp only [generalLinearBorelWeight_apply, zpow_add, Finset.prod_mul_distrib]
  rw [generalLinearBorel_det, Finset.prod_zpow]

/-- Multiplication by the original determinant power carries the exact induced functions to the shifted source weight. -/
theorem generalLinearIntegralInduced_determinant_twist (lam : Fin n → ℤ) (c : ℤ)
    {p : GeneralLinearRegularFunctions R n}
    (hp : p ∈ generalLinearIntegralInducedSubmodule R n lam) :
    ((generalLinearRegularDeterminantUnit ^ c : (GeneralLinearRegularFunctions R n)ˣ) :
        GeneralLinearRegularFunctions R n) * p ∈
      generalLinearIntegralInducedSubmodule R n (fun i => lam i + c) := by
  intro A _ _ g b
  simp only [map_mul, generalLinearRegularEval_determinant_zpow,
    hp A g b, generalLinearBorelWeight_shift, mul_zpow, Units.val_mul]
  ring

/-- The original determinant power gives a linear equivalence between the exact source induced modules at weights differing by a constant tuple. -/
def generalLinearIntegralInducedDeterminantEquiv (lam : Fin n → ℤ) (c : ℤ) :
    generalLinearIntegralInducedSubmodule R n lam ≃ₗ[R]
      generalLinearIntegralInducedSubmodule R n (fun i => lam i + c) where
  toFun p := ⟨_, generalLinearIntegralInduced_determinant_twist lam c p.property⟩
  invFun p := ⟨((generalLinearRegularDeterminantUnit ^ (-c) :
      (GeneralLinearRegularFunctions R n)ˣ) : GeneralLinearRegularFunctions R n) * p.val,
    by simpa only [add_neg_cancel_right] using
      generalLinearIntegralInduced_determinant_twist (fun i => lam i + c) (-c) p.property⟩
  left_inv p := by
    apply Subtype.ext
    change ((generalLinearRegularDeterminantUnit ^ (-c) :
      (GeneralLinearRegularFunctions R n)ˣ) : GeneralLinearRegularFunctions R n) *
      (((generalLinearRegularDeterminantUnit ^ c :
        (GeneralLinearRegularFunctions R n)ˣ) : GeneralLinearRegularFunctions R n) * p.val) = p.val
    simp [zpow_neg, ← mul_assoc]
  right_inv p := by
    apply Subtype.ext
    change ((generalLinearRegularDeterminantUnit ^ c :
      (GeneralLinearRegularFunctions R n)ˣ) : GeneralLinearRegularFunctions R n) *
      (((generalLinearRegularDeterminantUnit ^ (-c) :
        (GeneralLinearRegularFunctions R n)ˣ) : GeneralLinearRegularFunctions R n) * p.val) = p.val
    simp [zpow_neg, ← mul_assoc]
  map_add' p q := by
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' a p := by
    apply Subtype.ext
    change _ * (a • p.val) = a • (_ * p.val)
    simp only [Algebra.smul_def]
    ring

/-- Finite generation of the literal induced module is unchanged by the exact determinant twist. -/
theorem generalLinearIntegralInduced_finite_iff_shift (lam : Fin n → ℤ) (c : ℤ) :
    Module.Finite R (generalLinearIntegralInducedSubmodule R n lam) ↔
      Module.Finite R (generalLinearIntegralInducedSubmodule R n (fun i => lam i + c)) :=
  Module.Finite.equiv_iff (generalLinearIntegralInducedDeterminantEquiv lam c)

end
end Dubon2026
