import Dubon2026.SourceIntegralHeckeBasisCoordinates

/-! DUB-17/18 -> original rank-two matrix descent -> compare full
integral operator words on cusp forms and their duals. Actual Hecke
commutativity removes the reversal in transposition, so the same word
acts contragrediently without changing the integral operator relations.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Gamma0 N) 2

theorem sourceWeightTwoCuspHeckeWord_mem_integral (a : FreeAlgebra ℤ Nat.Primes) :
    sourceWeightTwoCuspHeckeWord N a ∈ sourceOriginalIntegralHeckeAlgebra N 2 := by
  have hle : Algebra.adjoin ℤ (Set.range fun q : Nat.Primes => cuspHeckeLinear N 2 q.val) ≤
      sourceOriginalIntegralHeckeAlgebra N 2 := by
    apply Algebra.adjoin_le
    rintro _ ⟨q, rfl⟩
    exact Algebra.subset_adjoin ⟨⟨q.val, q.property.pos⟩, rfl⟩
  have hr := Algebra.adjoin_range_eq_range_freeAlgebra_lift ℤ (X := Nat.Primes)
    (fun q : Nat.Primes => cuspHeckeLinear N 2 q.val)
  exact hle (hr.ge ⟨a, rfl⟩)

open scoped IsMulCommutative in
theorem sourceWeightTwoCuspHeckeWord_commute (a b : FreeAlgebra ℤ Nat.Primes) :
    Commute (sourceWeightTwoCuspHeckeWord N a) (sourceWeightTwoCuspHeckeWord N b) := by
  letI := sourceWeightTwoFullHeckeAlgebra_commutative N
  letI : CommRing (sourceWeightTwoFullHeckeAlgebra N) := inferInstance
  let ta : sourceWeightTwoFullHeckeAlgebra N := ⟨sourceWeightTwoCuspHeckeWord N a,
    sourceOriginalIntegralHecke_le_full N (sourceWeightTwoCuspHeckeWord_mem_integral N a)⟩
  let tb : sourceWeightTwoFullHeckeAlgebra N := ⟨sourceWeightTwoCuspHeckeWord N b,
    sourceOriginalIntegralHecke_le_full N (sourceWeightTwoCuspHeckeWord_mem_integral N b)⟩
  exact congrArg Subtype.val (mul_comm ta tb)

/-- The same integral prime word evaluated on the dual of the actual cusp space. -/
def sourceWeightTwoDualHeckeWord :
    FreeAlgebra ℤ Nat.Primes →ₐ[ℤ] Module.End ℂ (Module.Dual ℂ S) :=
  FreeAlgebra.lift ℤ (fun ell : Nat.Primes => (cuspHeckeLinear N 2 ell.val).dualMap)

private theorem integral_lift_cast {ι A : Type*} [Ring A] (t : ι → A) (r : ℤ) :
    FreeAlgebra.lift ℤ t (algebraMap ℤ (FreeAlgebra ℤ ι) r) = (r : A) := by
  rw [AlgHom.commutes, algebraMap_int_eq, eq_intCast]

theorem sourceWeightTwoDualHeckeWord_apply (a : FreeAlgebra ℤ Nat.Primes)
    (φ : Module.Dual ℂ S) (f : S) :
    sourceWeightTwoDualHeckeWord N a φ f = φ (sourceWeightTwoCuspHeckeWord N a f) := by
  induction a using FreeAlgebra.induction generalizing φ f with
  | grade0 r =>
    dsimp only [sourceWeightTwoDualHeckeWord, sourceWeightTwoCuspHeckeWord]
    rw [integral_lift_cast, integral_lift_cast, Module.End.intCast_apply,
      Module.End.intCast_apply, LinearMap.smul_apply, map_zsmul]
  | grade1 ell =>
    simp only [sourceWeightTwoDualHeckeWord, sourceWeightTwoCuspHeckeWord,
      FreeAlgebra.lift_ι_apply, LinearMap.dualMap_apply]
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
    exact congrArg φ (congrArg (fun T : Module.End ℂ S => T f)
      (sourceWeightTwoCuspHeckeWord_commute N b a).eq)
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      LinearMap.add_apply, map_add, ha, hb]

end
end Dubon2026
