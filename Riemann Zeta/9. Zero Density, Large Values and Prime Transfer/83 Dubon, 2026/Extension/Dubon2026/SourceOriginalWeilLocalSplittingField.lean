import Dubon2026.SourceOriginalWeilConvergentKummerRoot
import Mathlib.FieldTheory.KummerExtension

/-! DUB-17/18 -> auxiliary cover analytic entry -> actual local field map.
The locally proved convergent root and constant roots of unity split the
literal polynomial. The pinned splitting-field universal property embeds
the actual auxiliary field, extending the original chart homomorphism.
This proves local realization, not global cover geometry or divisibility. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve CuspTaylor Polynomial
variable (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldOver N ℂ

theorem exists_originalWeil_local_splittingField (n : ℕ) [NeZero n]
    (D : Divisor ℂ FF) (f : FF) (hf : f ≠ 0)
    (hfD : ∀ v : Place ℂ FF, v.ord f = (n : ℤ) * D v) (v : Place ℂ FF) :
    ∃ e : Polynomial.SplittingField (X ^ n - C f) →ₐ[ℂ] realizedField,
      ∀ g : FF, e (algebraMap FF (Polynomial.SplittingField (X ^ n - C f)) g) =
        chartLaurentHom N v g := by
  obtain ⟨A, hA⟩ := exists_originalWeil_convergent_kummer_root N n D f hf hfD v
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ n
  letI : Algebra FF realizedField := (chartLaurentHom N v).toAlgebra
  haveI : IsScalarTower ℂ FF realizedField := IsScalarTower.of_algebraMap_eq
    (fun c => (chartLaurentHom N v).commutes c |>.symm)
  have hs : ((X ^ n - C f).map (algebraMap FF realizedField)).Splits := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hζ.map_of_injective (algebraMap ℂ realizedField).injective) hA
  let e := Polynomial.SplittingField.lift (X ^ n - C f) hs
  exact ⟨e.restrictScalars ℂ, fun g => e.commutes g⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
