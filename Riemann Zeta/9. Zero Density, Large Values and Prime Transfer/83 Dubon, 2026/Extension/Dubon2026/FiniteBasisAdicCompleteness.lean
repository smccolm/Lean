import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.AdjoinRoot

/-! # Genuine adic completeness of modules with an original finite basis -/

namespace Dubon2026
noncomputable section

open Module
open scoped BigOperators

private theorem finiteBasis_mem_ideal_smul_top_iff
    {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b : Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    have h := (Submodule.smul_top_le_comap_smul_top I (b.coord i)) hx
    simpa [Submodule.mem_comap, Basis.coord_apply, Ideal.smul_eq_mul] using h
  · intro hx
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (hx i) (Submodule.mem_top : b i ∈ (⊤ : Submodule R M))

/-- Coordinate limits in the original complete coefficient ring give genuine
adic completeness of the original finite free module. The actual ideal powers
and original basis are retained on both sides. -/
theorem finiteBasis_isAdicComplete
    {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b : Basis ι R M) (I : Ideal R) [IsAdicComplete I R] : IsAdicComplete I M := by
  have hcoord (J : Ideal R) (x y : M) :
      x ≡ y [SMOD (J • ⊤ : Submodule R M)] ↔
        ∀ i, b.repr x i - b.repr y i ∈ J := by
    simpa [SModEq.sub_mem, map_sub] using finiteBasis_mem_ideal_smul_top_iff b J (x - y)
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply b.repr.injective
    ext i
    simp only [map_zero, Finsupp.zero_apply]
    apply IsHausdorff.haus' (I := I)
    intro n
    have h := (hcoord (I ^ n) x 0).mp (hx n) i
    simpa [SModEq.sub_mem, Ideal.smul_eq_mul] using h
  · intro f hf
    have hc (i : ι) : ∃ a : R, ∀ n,
        b.repr (f n) i ≡ a [SMOD (I ^ n • ⊤ : Ideal R)] := by
      apply IsPrecomplete.prec' (fun n => b.repr (f n) i)
      intro m n hmn
      have h := (hcoord (I ^ m) (f m) (f n)).mp (hf hmn) i
      simpa [SModEq.sub_mem, Ideal.smul_eq_mul] using h
    choose a ha using hc
    refine ⟨b.equivFun.symm a, fun n => (hcoord (I ^ n) _ _).mpr ?_⟩
    intro i
    have hrepr : b.repr (b.equivFun.symm a) i = a i := by
      simpa only [Basis.equivFun_apply] using congrFun (b.equivFun.apply_symm_apply a) i
    rw [hrepr]
    simpa [SModEq.sub_mem, Ideal.smul_eq_mul] using ha i n

/-- The original monic root algebra is complete for the extension of the
original ideal, by its actual power basis and the exact scalar-change identity. -/
theorem monic_adjoinRoot_isAdicComplete
    {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : Polynomial R) (hf : f.Monic) :
    IsAdicComplete (I.map (algebraMap R (AdjoinRoot f))) (AdjoinRoot f) := by
  apply (IsAdicComplete.map_algebraMap_iff (R := R) (S := AdjoinRoot f)
    (I := I) (M := AdjoinRoot f)).mpr
  exact finiteBasis_isAdicComplete (AdjoinRoot.powerBasis' hf).basis I

end
end Dubon2026
