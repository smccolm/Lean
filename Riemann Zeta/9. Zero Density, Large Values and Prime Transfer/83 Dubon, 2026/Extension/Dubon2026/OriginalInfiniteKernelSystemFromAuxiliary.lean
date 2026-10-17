import Dubon2026.OriginalInfiniteKernelClassSystem
import Dubon2026.OriginalClassInvariantFromInflatedInfiniteKernel
import Dubon2026.OriginalIdeleGeneratorBaseChangeTransfer
import Dubon2026.OriginalClassFullOrderFromSpan

/-! # Canonical class normalization from the actual auxiliary idele

Use the existing scaled generator transfer, retaining its inflation
identity. The normalized auxiliary total scales to the reciprocal target
degree. Principal reciprocity then identifies the invariant on target
ideles with zero original infinite localization. This is the assembled finite-tower step on DUB-17's class-formation
dependency; its arithmetic field and reciprocity inputs remain explicit.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

private theorem scaled_reciprocal (n d : ℕ) (hn : n ≠ 0) (hd : d ≠ 0) (hdn : d ∣ n) :
    (n / d) • (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) = ↑((1 : ℚ) / d) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  rw [Nat.cast_div hdn]
  field_simp
  exact_mod_cast hd

variable (K E L M : Type) [Field K] [NumberField K]
  [Field E] [NumberField E] [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K E] [IsGalois K L] [IsGalois K M]

/-- The genuine auxiliary full-idele witness constructs injective global and subgroup class invariants with exact images, the restriction-index formula, and the target total formula on the zero-infinite part. -/
theorem originalIdeleClass_infinite_kernel_system_of_auxiliary_idele
    (totalE : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
    (totalL : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (totalM : groupCohomology (originalFullIdeleRep K M) 2 →+ AddCircle (1 : ℚ))
    (hE : ∀ x, totalM (originalFullIdeleBaseChangeH2 K K E M x) = totalE x)
    (hL : ∀ x, totalM (originalFullIdeleBaseChangeH2 K K L M x) = totalL x)
    (hkernel : ∀ x,
      (∀ v : NumberField.InfinitePlace M, originalFullIdeleInfiniteH2 K M v x = 0) →
      (groupCohomology.functor ℤ Gal(M/K) 2).map
      (originalFullClassRepHom K M) x = 0 → totalM x = 0)
    (n : ℕ) (hd : Module.finrank K E ∣ n) (hn : n ≠ 0)
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : addOrderOf ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalFullClassRepHom K L) x) = n)
    (hz : (groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullClassRepHom E M)
      ((n / Module.finrank K E) • originalFullIdeleBaseChangeH2 K E L M x) = 0)
    (ht : totalL x = ↑((1 : ℚ) / n))
    (hInf : ∀ v : NumberField.InfinitePlace L, originalFullIdeleInfiniteH2 K L v x = 0) :
    OriginalInfiniteKernelClassInvariantSystem K E totalE := by
  letI : FiniteDimensional K E := FiniteDimensional.left K E M
  obtain ⟨u, hc, hs, hi⟩ := originalIdeleClass_generator_of_idele_baseChange_zero
    K E L M n hd hn x hx hz
  have hu := originalIdeleClass_full_order_of_span K E u hc hs
  obtain ⟨invG, hG, hR, hN, hS⟩ := originalIdeleClass_exists_invariants_of_full_order K E u hu
  let y : groupCohomology (originalFullIdeleRep K L) 2 := (n / Module.finrank K E) • x
  have hty : totalL y = ↑((1 : ℚ) / Module.finrank K E) := by
    change totalL ((n / Module.finrank K E) • x) = _
    rw [map_nsmul, ht]
    exact scaled_reciprocal n (Module.finrank K E) hn
      (Module.finrank_pos (R := K) (M := E)).ne' hd
  have hiy : groupCohomology.map (AlgEquiv.restrictNormalHom E)
      (originalIdeleClassTowerInclusion K E M) 2 u =
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (originalIdeleClassTowerInclusion K L M) 2
        ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) y) := by
    let P : groupCohomology (originalFullIdeleRep K L) 2 →+
        groupCohomology (originalIdeleClassRep K L) 2 :=
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)).hom.toAddMonoidHom
    let i := (groupCohomology.map (AlgEquiv.restrictNormalHom L)
      (originalIdeleClassTowerInclusion K L M) 2).hom.toAddMonoidHom
    change _ = i (P ((n / Module.finrank K E) • x))
    rw [map_nsmul, map_nsmul]
    exact hi
  exact ⟨invG, hG, hR,
    originalIdeleClass_invariant_total_of_inflated_idele_infinite_kernel K E L M totalE totalL totalM
      hE hL hkernel u hu y hiy invG (hN.trans hty.symm) (fun v =>
        (map_nsmul (originalFullIdeleInfiniteH2 K L v).hom (n / Module.finrank K E) x).trans
          ((congrArg (fun z => (n / Module.finrank K E) • z) (hInf v)).trans (nsmul_zero _))), hS⟩

end
end Dubon2026
