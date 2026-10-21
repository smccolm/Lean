import Mathlib.Algebra.Algebra.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Basic

/-! Prime-field coordinates of the tensor extension used in residual binary H1.
DUB-17/18 -> residual modular Galois association -> nonzero residual H1
eigensystem -> injective tensor coefficient change -> finite coordinate expansion.

Adapted from Coordinates and exists_finsupp_eq_sum in
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_injective_baseChange_coeffH1_binaryFormRepSL.lean
(Apache-2.0; retained LICENSE and NOTICE).
-/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {ell : ℕ} {F ι : Type} [Field F] [Algebra (ZMod ell) F]

/-- An additive coordinate in the actual coefficient field over its prime field. -/
def sourceResidualCoordinate (b : Module.Basis ι (ZMod ell) F) (j : ι) : F →+ ZMod ell where
  toFun x := b.repr x j
  map_zero' := by simp
  map_add' x y := by simp

open Classical in
/-- A prime-field basis coordinate of an integer multiple has its literal residue value. -/
theorem sourceResidualCoordinate_basis_intCast (b : Module.Basis ι (ZMod ell) F)
    (i j : ι) (a : ℤ) :
    sourceResidualCoordinate b j (b i * (a : F)) = if i = j then (a : ZMod ell) else 0 := by
  classical
  have h : b i * (a : F) = (a : ZMod ell) • b i := by
    rw [Algebra.smul_def, map_intCast, mul_comm]
  rw [h]
  change b.repr ((a : ZMod ell) • b i) j = _
  rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs <;> simp

private theorem zmod_smul_integer [NeZero ell] (a : ZMod ell) (x : F) :
    a • x = (a.val : ℤ) • x := by
  calc
    a • x = (a.val : ZMod ell) • x := congrArg (· • x) (ZMod.natCast_zmod_val a).symm
    _ = (a.val : ℤ) • x := by rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

/-- Every tensor over Z has a finite expansion in the chosen residue-field basis,
with coefficients in the actual original integral module. -/
theorem sourceResidualTensor_exists_finsupp [NeZero ell]
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis ι (ZMod ell) F) (y : F ⊗[ℤ] M) :
    ∃ f : ι →₀ M, y = f.sum fun j m => b j ⊗ₜ[ℤ] m := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [Finsupp.sum_zero_index]⟩
  | tmul c x =>
    refine ⟨(b.repr c).mapRange (fun a => (a.val : ℤ) • x) (by simp), ?_⟩
    rw [Finsupp.sum_mapRange_index (fun _ => by rw [TensorProduct.tmul_zero])]
    have hc : c = (b.repr c).sum fun j a => a • b j := by
      conv_lhs => rw [← b.linearCombination_repr c]
      rw [Finsupp.linearCombination_apply]
    conv_lhs => rw [hc]
    rw [Finsupp.sum, Finsupp.sum, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zmod_smul_integer]
    exact (TensorProduct.CompatibleSMul.int (R := ℤ) (M := F) (P := M)).smul_tmul
      (((b.repr c) j).val : ℤ) (b j) x
  | add x y hx hy =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := hy
    refine ⟨f + g, ?_⟩
    rw [Finsupp.sum_add_index']
    · intro j
      rw [TensorProduct.tmul_zero]
    · intro j m n
      rw [TensorProduct.tmul_add]

end
end Dubon2026
