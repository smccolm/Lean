import Dubon2026.SourceIntegralReductionExtension
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> prescribed cusp stabilizer chart. Reduce all
actual complex algebraic integers into the algebraically closed residue field
while sending the standard complex primitive root to a prescribed primitive
root. Native cyclotomic/minimal-polynomial evaluation handles the cyclotomic
subring, and the already proved integral-reduction extension handles the rest.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot.
The existing native extension theorem replaces its separate lying-over,
quotient-domain and algebraic-closure construction. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open Polynomial
local notation "Zbar" => integralClosure ℤ ℂ

theorem exists_algebraicIntegerReduction_primitiveRoot
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ζ : K) (hζ : IsPrimitiveRoot ζ N) :
    ∃ φ : Zbar →+* K, ∀ z : Zbar,
      (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N) → φ z = ζ := by
  letI : NeZero (N : K) := ⟨fun h => hℓN ((CharP.cast_eq_zero_iff K ℓ N).mp h)⟩
  let μ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hμ : IsPrimitiveRoot μ N := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hμint : IsIntegral ℤ μ := hμ.isIntegral (NeZero.pos N)
  let z : Zbar := ⟨μ, hμint⟩
  have hi : Function.Injective (algebraMap Zbar ℂ) := Subtype.val_injective
  have hz : IsIntegral ℤ z := (isIntegral_algHom_iff (integralClosure ℤ ℂ).val hi).mp hμint
  have hmin : minpoly ℤ z = cyclotomic N ℤ := by
    rw [← minpoly.algebraMap_eq hi z]
    exact (cyclotomic_eq_minpoly hμ (NeZero.pos N)).symm
  have hroot : Polynomial.eval₂ (Int.castRingHom K) ζ (minpoly ℤ z) = 0 := by
    rw [hmin, eval₂_eq_eval_map, map_cyclotomic_int, ← IsRoot.def, isRoot_cyclotomic_iff]
    exact hζ
  let B := Algebra.adjoin ℤ ({z} : Set Zbar)
  let χ : B →+* K := (AdjoinRoot.lift (Int.castRingHom K) ζ hroot).comp
    (minpoly.equivAdjoin hz).symm.toRingEquiv.toRingHom
  have hzB : z ∈ B := Algebra.self_mem_adjoin_singleton ℤ z
  have hχ : χ ⟨z, hzB⟩ = ζ := by
    have he : (minpoly.equivAdjoin hz).symm ⟨z, hzB⟩ = AdjoinRoot.root (minpoly ℤ z) := by
      rw [AlgEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [minpoly.coe_equivAdjoin]
      exact AdjoinRoot.Minpoly.coe_toAdjoin_mk_X.symm
    change AdjoinRoot.lift (Int.castRingHom K) ζ hroot
      ((minpoly.equivAdjoin hz).symm ⟨z, hzB⟩) = ζ
    rw [he, AdjoinRoot.lift_root]
  letI : Algebra.IsIntegral B Zbar := Algebra.IsIntegral.tower_top (R := ℤ)
  obtain ⟨φ, hφ⟩ := sourceIntegralReduction_exists_extension
    (show Function.Injective (algebraMap B Zbar) from Subtype.val_injective) χ
  refine ⟨φ, fun w hw => ?_⟩
  have hwz : w = z := Subtype.ext hw
  rw [hwz]
  exact (RingHom.congr_fun hφ ⟨z, hzB⟩).trans hχ

end
end Dubon2026.SourceFunctionField.IntegralSlash
