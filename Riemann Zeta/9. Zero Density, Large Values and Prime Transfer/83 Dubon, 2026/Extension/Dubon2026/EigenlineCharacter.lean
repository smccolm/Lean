import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Algebra characters from a genuine nonzero invariant eigenline -/

namespace Dubon2026

noncomputable section

variable {K A W : Type*} [Field K] [Ring A] [Algebra K A] [AddCommGroup W] [Module K W]

/-- The scalar action on an actual nonzero invariant line is a genuine algebra character. -/
def eigenlineCharacter (T : A →ₐ[K] Module.End K W) (v : W) (hv : v ≠ 0)
    (h : ∀ a : A, ∃ c : K, T a v = c • v) : A →ₐ[K] K := by
  let χ : A → K := fun a => Classical.choose (h a)
  have hχ (a : A) : T a v = χ a • v := Classical.choose_spec (h a)
  refine
    { toFun := χ
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · apply smul_left_injective K hv
    dsimp only
    rw [← hχ, map_one, one_smul]
    rfl
  · intro a b
    apply smul_left_injective K hv
    dsimp only
    rw [← hχ, map_mul, Module.End.mul_apply, hχ b, map_smul, hχ a, smul_smul,
      mul_comm (χ b) (χ a), mul_smul]
  · apply smul_left_injective K hv
    dsimp only
    rw [← hχ, map_zero, LinearMap.zero_apply, zero_smul]
  · intro a b
    apply smul_left_injective K hv
    dsimp only
    rw [← hχ, map_add, LinearMap.add_apply, hχ a, hχ b, add_smul]
  · intro a
    apply smul_left_injective K hv
    dsimp only
    rw [← hχ, T.commutes a]
    rfl

/-- The constructed character is exactly the scalar of the original action on the original line. -/
theorem eigenlineCharacter_spec (T : A →ₐ[K] Module.End K W) (v : W) (hv : v ≠ 0)
    (h : ∀ a : A, ∃ c : K, T a v = c • v) (a : A) :
    T a v = eigenlineCharacter T v hv h a • v := Classical.choose_spec (h a)

/-- An actual commuting endomorphism preserves each original eigenvector and its eigenvalue. -/
theorem commutingEnd_eigenvector (C T : Module.End K W) (v : W) (a : K)
    (hCT : Commute C T) (hv : C v = a • v) : C (T v) = a • T v := by
  calc
    C (T v) = T (C v) := congrArg (fun S : Module.End K W => S v) hCT.eq
    _ = T (a • v) := congrArg T hv
    _ = a • T v := T.map_smul a v

/-- The exact original generator eigenvalue propagates to its whole genuine algebraic cyclic span. -/
theorem commutingEnd_cyclicSpan (T : A →ₐ[K] Module.End K W) (C : Module.End K W)
    (v : W) (a : K) (hCT : ∀ z, Commute C (T z)) (hv : C v = a • v)
    (w : W) (hw : w ∈ Submodule.span K (Set.range (fun z => T z v))) : C w = a • w := by
  have hle : Submodule.span K (Set.range (fun z => T z v)) ≤ C.eigenspace a := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (commutingEnd_eigenvector C (T z) v a (hCT z) hv)
  exact Module.End.mem_eigenspace_iff.mp (hle hw)

end
end Dubon2026
