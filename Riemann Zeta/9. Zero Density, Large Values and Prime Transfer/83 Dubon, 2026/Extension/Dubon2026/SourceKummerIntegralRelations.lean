import Dubon2026.SourceCurveRegularProlongation
import Mathlib.FieldTheory.KummerExtension

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
distinct extending reductions. The native monic-divisibility descent
identifies the integral polynomial relations of a Kummer generator.
Consequently evaluation at each reduced root annihilates those relations,
which permits a genuine residue map on the integral generated algebra.
This replaces the external repeated polynomial remainder calculation. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open Polynomial
variable {L F Fbar E : Type*} [Field L] {A : ValuationSubring L}
  [Field F] [Algebra L F] [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
  [Field E] [Algebra F E]
variable (R : RegularProlongation A F Fbar) {q : ℕ} [hq : Fact q.Prime]

theorem kummer_relation_dvd (f : R.integers) (hf : ∀ g : F, g ^ q ≠ (f : F))
    {α : E} (hα : α ^ q = algebraMap F E (f : F))
    (p : R.integers[X]) (hp : aeval α (p.map R.integers.subtype) = 0) :
    X ^ q - C f ∣ p := by
  have hmin : minpoly F α = X ^ q - C (f : F) :=
    (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hq.out hf)
      (by simp only [map_sub, map_pow, aeval_X, aeval_C, hα, sub_self])
      (monic_X_pow_sub_C (f : F) hq.out.ne_zero)).symm
  apply (Polynomial.map_dvd_map R.integers.subtype Subtype.val_injective
    (monic_X_pow_sub_C f hq.out.ne_zero)).mp
  rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  change X ^ q - C (f : F) ∣ p.map R.integers.subtype
  rw [← hmin]
  exact minpoly.dvd F α hp

theorem kummer_residue_eval_zero_of_relation
    (f : R.integers) (hf : ∀ g : F, g ^ q ≠ (f : F))
    {α : E} (hα : α ^ q = algebraMap F E (f : F))
    {s : Fbar} (hs : s ^ q = R.residue f)
    (p : R.integers[X]) (hp : aeval α (p.map R.integers.subtype) = 0) :
    eval₂ R.residue s p = 0 := by
  obtain ⟨g, hg⟩ := R.kummer_relation_dvd f hf hα p hp
  rw [hg, eval₂_mul, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hs, sub_self, zero_mul]

end
end Dubon2026.SourceCurve.RegularProlongation
