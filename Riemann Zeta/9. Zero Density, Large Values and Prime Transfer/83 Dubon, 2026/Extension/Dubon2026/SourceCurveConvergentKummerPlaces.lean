import Dubon2026.SourceCurveConvergentGaloisPlaces
import Mathlib.FieldTheory.KummerExtension

/-! DUB-17/18 -> actual torsion-cover charts -> normalized local embeddings.
The literal nonzero Kummer polynomial is separable, so native Galois place
transitivity applies to its actual splitting field. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open SourceFunctionField.CuspTaylor Polynomial
variable {F : Type*} [Field F] [Algebra ℂ F]
variable (n : ℕ) [NeZero n] (f : F)
local notation "EE" => SplittingField (X ^ n - C f : F[X])

local instance kummerFinite : FiniteDimensional F EE :=
  Polynomial.IsSplittingField.finiteDimensional EE (X ^ n - C f)

local instance kummerIntegral : Algebra.IsIntegral F EE :=
  Algebra.IsIntegral.of_finite F EE

theorem exists_normalized_convergent_kummer_embedding (hf : f ≠ 0)
    (w : Place ℂ EE) (ι : F →ₐ[ℂ] realizedField)
    (hex : ∃ (w₀ : Place ℂ EE) (e : EE →ₐ[ℂ] realizedField),
      w₀.restrict F = w.restrict F ∧
      (∀ g : F, e (algebraMap F EE g) = ι g) ∧
      ∀ a : EE, w₀.ord a = (e a).val.order) :
    ∃ e : EE →ₐ[ℂ] realizedField,
      (∀ g : F, e (algebraMap F EE g) = ι g) ∧
      ∀ a : EE, w.ord a = (e a).val.order := by
  haveI : CharZero F := Algebra.charZero_of_charZero ℂ F
  haveI : IsGalois F EE := IsGalois.of_separable_splitting_field
    (separable_X_pow_sub_C f (by exact_mod_cast NeZero.ne n) hf)
  exact exists_normalized_convergent_embedding w ι hex

end
end Dubon2026.SourceCurve.Place
