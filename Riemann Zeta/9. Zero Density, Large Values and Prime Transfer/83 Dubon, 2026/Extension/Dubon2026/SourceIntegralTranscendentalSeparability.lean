import Dubon2026.SourceIntegralPrimeLaurentRoots
import Dubon2026.SourceOriginalSlotRange
import Dubon2026.SourceModularJTranscendence
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17/18 -> residual inertia -> modular-curve good reduction -> cyclic
subgroup orbit census -> generic-fiber injectivity. Transfer the already proved
Laurent separability through the native rational-function field. The statement
requires transcendental j; it makes no assertion about exceptional CM fibers. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial IntermediateField
noncomputable section

/-- Integer polynomial specialization at a transcendental element preserves separability. -/
theorem relationAtSeed_separable_iff_ratFunc
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (P : Polynomial (Polynomial ℤ)) (x : L) (hx : Transcendental K x) :
    (relationAtSeed P x).Separable ↔
      (relationAtSeed P (RatFunc.X : RatFunc K)).Separable := by
  let e : RatFunc K →ₐ[K] L :=
    (K⟮x⟯.val).comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom
  have he : e.toRingHom RatFunc.X = x := RatFunc.algEquivOfTranscendental_X x hx
  have hm := relationAtSeed_map P (RatFunc.X : RatFunc K) e.toRingHom
  rw [he] at hm
  rw [← hm]
  exact Polynomial.separable_map e.toRingHom

/-- The expanded original j-series remains transcendental over its constants. -/
theorem transcendental_qExpand_jqModC (K : Type*) [Field K]
    (n : ℕ) [NeZero n] : Transcendental K (qExpand K n (jqModC K)) := by
  intro h
  exact transcendental_jqModC K
    ((isAlgebraic_algHom_iff (qExpandAlgHom K n) (qExpandAlgHom K n).injective).mp h)

/-- At any transcendental j-coordinate, the prime modular polynomial is separable away from the characteristic. -/
theorem modularPolynomial_prime_separable_transcendental
    {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0)
    (j : L) (hj : Transcendental K j) :
    (relationAtSeed (modularPolynomial p) j).Separable := by
  haveI : NeZero (p : K) := ⟨hp⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  obtain ⟨ζ, hζval⟩ := hz.isUnit (Nat.Prime.ne_zero (Fact.out : p.Prime))
  have hζ : IsPrimitiveRoot (ζ : K) p := hζval.symm ▸ hz
  apply (relationAtSeed_separable_iff_ratFunc (K := K) _ j hj).mpr
  exact (relationAtSeed_separable_iff_ratFunc (K := K) _ _
    (transcendental_qExpand_jqModC K p)).mp
      (modularPolynomial_prime_laurent_separable K p ζ hζ)

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
