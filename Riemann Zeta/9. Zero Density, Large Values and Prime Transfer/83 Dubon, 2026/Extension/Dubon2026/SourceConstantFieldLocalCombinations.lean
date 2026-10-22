import Dubon2026.SourceCurveOrders

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> exact constant-field place extension. These finite local combinations and their
fractions express every original complex function in a form whose order can
be computed from the original arithmetic place. This serves the conorm of
divisors and preserves the literal principal-divisor relation.
Adapted from S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Existing place orders are reused.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section

variable {K F K' : Type*} (F' : Type*) [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  {ι : Type*} (B : Module.Basis ι K K') (P : Place K F)

/-- The finite complex-linear combination of original valuation-ring coefficients. -/
noncomputable def Psi : (ι →₀ P.toValuationSubring) →+ F' :=
  Finsupp.liftAddHom fun j =>
    (AddMonoidHom.mulLeft (algebraMap K' F' (B j))).comp
      ((algebraMap F F' : F →+* F').toAddMonoidHom.comp
        P.toValuationSubring.subtype.toAddMonoidHom)

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_single (j : ι) (o : P.toValuationSubring) :
    Psi F' B P (Finsupp.single j o) = algebraMap K' F' (B j) * algebraMap F F' (o : F) := by
  simp [Psi]

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_apply (w : ι →₀ P.toValuationSubring) :
    Psi F' B P w = w.sum fun j o => algebraMap K' F' (B j) * algebraMap F F' (o : F) := by
  rw [Psi, Finsupp.liftAddHom_apply]
  rfl

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_smul (s : P.toValuationSubring) (w : ι →₀ P.toValuationSubring) :
    Psi F' B P (s • w) = algebraMap F F' (s : F) * Psi F' B P w := by
  induction w using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [smul_add, map_add, map_add, ih, Finsupp.smul_single, Psi_single, Psi_single, mul_add,
      smul_eq_mul, MulMemClass.coe_mul, map_mul]
    ring

/-- The coefficient vector expressing a scalar multiple of an original local element. -/
noncomputable def pureW (d : K') (o : P.toValuationSubring) : ι →₀ P.toValuationSubring :=
  (B.repr d).mapRange (fun a => algebraMap K P.toValuationSubring a * o) (by simp)

theorem Psi_pureW (d : K') (o : P.toValuationSubring) :
    Psi F' B P (pureW B P d o) = algebraMap K' F' d * algebraMap F F' (o : F) := by
  rw [Psi_apply, pureW, Finsupp.sum_mapRange_index (fun j => by simp)]
  conv_rhs => rw [← B.linearCombination_repr d, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MulMemClass.coe_mul, Place.coe_algebraMap, map_mul, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  ring


end
end Dubon2026.SourceCurve.ConstantField
