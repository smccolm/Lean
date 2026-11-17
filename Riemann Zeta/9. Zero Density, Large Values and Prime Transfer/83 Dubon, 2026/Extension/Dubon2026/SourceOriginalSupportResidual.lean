import Dubon2026.SourceOriginalSupportCyclotomic
import Dubon2026.SourceOriginalRationalBottomRestriction
import Dubon2026.SourceArithmeticWeightTwist

/-! DUB-17/18 -> actual CM residual construction. The existing surjective
restriction enlarges the support of the same representation. Its cyclotomic
determinant and finite linear subfield bounds are proved unchanged. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix
open scoped NumberField

/-- The original coefficient-valued cyclotomic character respects support
restriction, including its actual residual scalar map. -/
theorem original_support_cyclotomic_unit_compatibility
    (a b : 𝓞 ℚ) (hab : a ∣ b) (p : ℕ) [NeZero p]
    {L : Type} [Field L] [CharP L p] [TopologicalSpace L]
    (hpa : (p : 𝓞 ℚ) ∣ a) (hpb : (p : 𝓞 ℚ) ∣ b)
    (g : rationalArithmeticGaloisGroup b) :
    sourceArithmeticCyclotomicUnitCharacter (F := L) p a hpa
        (rationalArithmeticSupportRestriction a b hab g) =
      sourceArithmeticCyclotomicUnitCharacter (F := L) p b hpb g := by
  change Units.map (ZMod.castHom (dvd_refl p) L).toMonoidHom
    (rationalArithmeticCyclotomicCharacter a p hpa
      (rationalArithmeticSupportRestriction a b hab g)) = _
  rw [original_support_cyclotomic_compatibility a b hab p hpa hpb g]
  rfl

/-- The same original cyclotomic determinant holds after enlarging support;
its compatibility is derived on genuine roots rather than supplied. -/
theorem original_support_residual_determinant
    (a b : 𝓞 ℚ) (hab : a ∣ b) (p w : ℕ) [NeZero p]
    {L : Type} [Field L] [CharP L p] [TopologicalSpace L]
    (hpa : (p : 𝓞 ℚ) ∣ a) (hpb : (p : 𝓞 ℚ) ∣ b)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) L)
    (hdet : GeneralLinearGroup.det.comp ρ =
      (sourceArithmeticCyclotomicUnitCharacter (F := L) p a hpa).toMonoidHom ^ w) :
    GeneralLinearGroup.det.comp
        (ρ.comp (rationalArithmeticSupportRestriction a b hab).toMonoidHom) =
      (sourceArithmeticCyclotomicUnitCharacter (F := L) p b hpb).toMonoidHom ^ w := by
  apply MonoidHom.ext
  intro g
  have h := DFunLike.congr_fun hdet (rationalArithmeticSupportRestriction a b hab g)
  change GeneralLinearGroup.det (ρ (rationalArithmeticSupportRestriction a b hab g)) =
    sourceArithmeticCyclotomicUnitCharacter (F := L) p a hpa
      (rationalArithmeticSupportRestriction a b hab g) ^ w at h
  simpa only [original_support_cyclotomic_unit_compatibility a b hab p hpa hpb g] using h

/-- Surjectivity of the genuine restriction retains exactly the original
finite linear subfield bounds. -/
theorem original_support_finite_linear_bounds
    (a b : 𝓞 ℚ) (hab : a ∣ b) (p : ℕ) [Fact p.Prime]
    {L : Type} [Field L] (j : L →+* K p)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) L)
    (h : HasFiniteLinearSubfieldBounds p j ρ) :
    HasFiniteLinearSubfieldBounds p j
      (ρ.comp (rationalArithmeticSupportRestriction a b hab).toMonoidHom) := by
  exact finite_linear_bounds_precomp_surjective p j ρ
    (rationalArithmeticSupportRestriction a b hab).toMonoidHom
    (rationalArithmeticSupportRestriction_surjective a b hab) h

end
end Dubon2026.SourceDickson
