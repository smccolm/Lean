import Dubon2026.SourceLaurentCoefficientMap
import Dubon2026.SourceTranscendentalTranslation
import Mathlib.Algebra.CharZero.Infinite

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond descent -> algebraic coefficients of the original translated field.
A transcendental coefficient would give infinitely many roots of the same
nonzero polynomial by the already proved constant-translation automorphisms.
Only the literal Laurent coefficient map and native polynomial roots are used.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem isAlgebraic_laurent_coeff_of_relation
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : Polynomial (LaurentSeries K)) (hp : p ≠ 0) (x : LaurentSeries L)
    (hx : Polynomial.eval₂ (coeffMap (algebraMap K L)) x p = 0) (n : ℤ) :
    IsAlgebraic K (x.coeff n) := by
  classical
  by_contra ht
  choose σ hσ using fun a : K =>
    SourceCurve.ConstantField.exists_translation_of_transcendental K L (x.coeff n) ht a
  let ι := coeffMap (algebraMap K L)
  let φ (a : K) := coeffMap (σ a).toRingHom
  have hc (a : K) : (φ a).comp ι = ι := by
    ext y m
    change σ a (algebraMap K L (y.coeff m)) = algebraMap K L (y.coeff m)
    exact (σ a).commutes _
  have hr (a : K) : (p.map ι).IsRoot (φ a x) := by
    have he := congrArg (φ a) hx
    rw [Polynomial.hom_eval₂, hc, map_zero] at he
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using he
  have hi : Function.Injective (fun a : K => φ a x) := by
    intro a b hab
    have he := congrArg (fun z : LaurentSeries L => z.coeff n) hab
    change σ a (x.coeff n) = σ b (x.coeff n) at he
    rw [hσ, hσ] at he
    exact (algebraMap K L).injective (add_left_cancel he)
  have hf : (Set.range fun a : K => φ a x).Finite :=
    (Polynomial.finite_setOf_isRoot (Polynomial.map_ne_zero hp)).subset (by
      rintro z ⟨a, rfl⟩
      exact hr a)
  exact (Set.infinite_range_of_injective hi) hf

end
end Dubon2026.SourceFunctionField
