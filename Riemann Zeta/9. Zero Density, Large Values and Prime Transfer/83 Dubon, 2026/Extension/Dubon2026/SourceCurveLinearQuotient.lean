import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.Tactic

/-! DUB-17/18 -> function-field Riemann--Roch -> finite local quotient
dimensions -> addition of dimensions in a nested quotient. Adapted from
the selected chain argument in S_AlgebraicCurve_finiteDimensional_lSpace,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The pinned third isomorphism
theorem and finite-submodule/quotient theorem supply the underlying facts.
-/
namespace Dubon2026.SourceCurve.LinearQuotient
noncomputable section
open Submodule Module
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

/-- The intermediate quotient in a nested submodule chain. -/
def nestedComapMapMkQEquiv {A B C : Submodule K X} (hBC : B ≤ C) :
    ((B.comap C.subtype).map (A.comap C.subtype).mkQ : Submodule K _)
      ≃ₗ[K] B ⧸ A.comap B.subtype := by
  set S := A.comap C.subtype with hS
  set T := B.comap C.subtype with hT

  let ψ : (T : Type _) →ₗ[K] (C ⧸ S) := S.mkQ ∘ₗ T.subtype
  have hker : LinearMap.ker ψ = S.comap T.subtype := by
    simp only [ψ, LinearMap.ker_comp, ker_mkQ]
  have hran : LinearMap.range ψ = T.map S.mkQ := by
    simp only [ψ, LinearMap.range_comp, range_subtype]
  let e1 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (T.map S.mkQ : Submodule K _) :=
    (Submodule.Quotient.equiv _ (LinearMap.ker ψ) (LinearEquiv.refl K T)
        (by rw [hker]; simp)).trans
      (ψ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hran))

  have hmap : (S.comap T.subtype).map
      (Submodule.comapSubtypeEquivOfLe hBC : (T : Type _) →ₗ[K] B) = A.comap B.subtype := by
    ext ⟨b, hb⟩
    simp only [mem_map, mem_comap, Submodule.coe_subtype, hS]
    constructor
    · rintro ⟨⟨⟨x, hxC⟩, hxB⟩, hxA, hxeq⟩
      have hx : x = b := congrArg Subtype.val hxeq
      subst hx; exact hxA
    · intro hbA
      exact ⟨⟨⟨b, hBC hb⟩, hb⟩, hbA, rfl⟩
  let e2 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (B ⧸ A.comap B.subtype) :=
    Submodule.Quotient.equiv _ _ (Submodule.comapSubtypeEquivOfLe hBC) hmap
  exact e1.symm.trans e2

theorem finrank_quotient_chain {A B C : Submodule K X} (hAB : A ≤ B) (hBC : B ≤ C)
    [hCB : Module.Finite K (C ⧸ B.comap C.subtype)]
    [hBA : Module.Finite K (B ⧸ A.comap B.subtype)] :
    Module.Finite K (C ⧸ A.comap C.subtype) ∧
      finrank K (C ⧸ A.comap C.subtype)
        = finrank K (C ⧸ B.comap C.subtype) + finrank K (B ⧸ A.comap B.subtype) := by
  set S := A.comap C.subtype
  set T := B.comap C.subtype
  have hST : S ≤ T := comap_mono hAB

  have e3 := Submodule.quotientQuotientEquivQuotient S T hST

  have eK := nestedComapMapMkQEquiv (K := K) (A := A) hBC
  haveI : Module.Finite K (T.map S.mkQ : Submodule K _) := Module.Finite.equiv eK.symm
  haveI : Module.Finite K ((C ⧸ S) ⧸ T.map S.mkQ) := Module.Finite.equiv e3.symm
  haveI hfin : Module.Finite K (C ⧸ S) := Module.Finite.of_submodule_quotient (T.map S.mkQ)
  refine ⟨hfin, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank (R := K) (T.map S.mkQ)
  rw [LinearEquiv.finrank_eq e3, LinearEquiv.finrank_eq eK] at h
  omega


end
end Dubon2026.SourceCurve.LinearQuotient
