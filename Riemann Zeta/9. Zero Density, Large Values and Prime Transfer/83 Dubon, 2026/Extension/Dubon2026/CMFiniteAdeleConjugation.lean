import Dubon2026.NumberFieldFiniteAdeleGaloisAction
import Mathlib.NumberTheory.NumberField.CMField

/-! # Original CM conjugation on the finite adeles

For DUB-17's source unitary group, conjugation must permute the actual
finite places and act on their original completions. The repository's
proved Galois adelic action supplies precisely that map, including its
principal-field compatibility. No coordinatewise scalar proxy is used.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

/-- The original CM involution acting on the original finite adeles. -/
def cmFiniteAdeleConjugation : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 K) K :=
  numberFieldFiniteAdeleGaloisMap ℚ K ((IsCMField.complexConj K).restrictScalars ℚ)

/-- The actual adelic CM action is involutive. -/
theorem cmFiniteAdeleConjugation_involutive :
    Function.Involutive (cmFiniteAdeleConjugation K) := by
  intro a
  let σ : Gal(K/ℚ) := (IsCMField.complexConj K).restrictScalars ℚ
  have hσ : σ * σ = 1 := by
    ext x
    exact IsCMField.complexConj_apply_apply K x
  change numberFieldFiniteAdeleGaloisMap ℚ K σ (numberFieldFiniteAdeleGaloisMap ℚ K σ a) = a
  rw [← numberFieldFiniteAdeleGaloisMap_mul, hσ, numberFieldFiniteAdeleGaloisMap_one]

/-- The actual adelic conjugation restricts to the original CM involution on principal elements. -/
theorem cmFiniteAdeleConjugation_algebraMap (x : K) :
    cmFiniteAdeleConjugation K (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) =
      algebraMap K (FiniteAdeleRing (𝓞 K) K) (star x) :=
  numberFieldFiniteAdeleGaloisMap_algebraMap ℚ K
    ((IsCMField.complexConj K).restrictScalars ℚ) x

/-- The actual finite-adelic star ring uses the original CM place-permuting involution. -/
@[reducible]
def cmFiniteAdeleStarRing : StarRing (FiniteAdeleRing (𝓞 K) K) where
  star := cmFiniteAdeleConjugation K
  star_involutive := cmFiniteAdeleConjugation_involutive K
  star_mul a b := ((cmFiniteAdeleConjugation K).map_mul a b).trans (mul_comm _ _)
  star_add := (cmFiniteAdeleConjugation K).map_add

/-- Original completed Galois continuity makes the actual adelic involution continuous. -/
theorem cmFiniteAdeleConjugation_continuous : Continuous (cmFiniteAdeleConjugation K) := by
  let σ : Gal(K/ℚ) := (IsCMField.complexConj K).restrictScalars ℚ
  let e := numberFieldGaloisPlaceEquiv ℚ K σ
  exact RestrictedProduct.mapAlong_continuous _ _ e.symm e.symm.injective.tendsto_cofinite
    (fun w => (numberFieldGaloisLocalTransport ℚ K σ (e.symm w) w
      (e.apply_symm_apply w)).toRingHom)
    (Filter.Eventually.of_forall fun w x hx => by
      change Valued.v (numberFieldGaloisLocalTransport ℚ K σ _ w _ x) ≤ 1
      rw [numberFieldGaloisLocalTransport_valuation]
      exact hx)
    (fun w => numberFieldGaloisLocalTransport_continuous ℚ K σ (e.symm w) w _)

end
end Dubon2026
