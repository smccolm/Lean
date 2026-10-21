import Dubon2026.SourceHeckeWordTransport

/-! DUB-17/18 -> residual Galois association -> original integral-span
weight-two eigensystem -> its character of the actual integral Hecke algebra.
The existing integral-word transport lemmas are specialized to complex
coefficients. The same kernel proof is needed over the actual residue field;
this version changes only that coefficient field, keeping the original
operators and coefficient map. The existing generic character construction
is reused directly. Provenance remains the Apache-2.0 source recorded in
SourceHeckeWordTransport and its retained LICENSE/NOTICE.
-/
namespace Dubon2026
noncomputable section

private theorem word_intCast {ι A : Type} [Ring A] (t : ι → A) (r : ℤ) :
    FreeAlgebra.lift ℤ t (algebraMap ℤ (FreeAlgebra ℤ ι) r) = (r : A) := by
  rw [AlgHom.commutes, algebraMap_int_eq, eq_intCast]

/-- Compatibility with every generating operator implies compatibility with every integral operator word. -/
theorem sourceResidualHeckeWord_intertwine {ι M V F : Type} [Field F]
    [AddCommGroup M] [Module ℤ M] [AddCommGroup V] [Module F V]
    (t : ι → Module.End ℤ M) (u : ι → Module.End F V) (Φ : M →+ V)
    (hΦ : ∀ i x, Φ (t i x) = u i (Φ x)) (a : FreeAlgebra ℤ ι) (x : M) :
    Φ (FreeAlgebra.lift ℤ t a x) = FreeAlgebra.lift ℤ u a (Φ x) := by
  induction a using FreeAlgebra.induction generalizing x with
  | grade0 r =>
    rw [word_intCast, word_intCast, Module.End.intCast_apply,
      Module.End.intCast_apply, map_zsmul]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, hΦ]
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]

/-- An actual common eigenvector evaluates every integral Hecke word at its original eigenvalues. -/
theorem sourceResidualHeckeWord_eigenvector {ι V F : Type} [Field F] [AddCommGroup V] [Module F V]
    (t : ι → Module.End F V) (lam : ι → F) (x : V)
    (hx : ∀ i, t i x = lam i • x) (a : FreeAlgebra ℤ ι) :
    FreeAlgebra.lift ℤ t a x = FreeAlgebra.lift ℤ lam a • x := by
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    rw [word_intCast, word_intCast, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, hx]
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, ha, hb, add_smul]

end
end Dubon2026
