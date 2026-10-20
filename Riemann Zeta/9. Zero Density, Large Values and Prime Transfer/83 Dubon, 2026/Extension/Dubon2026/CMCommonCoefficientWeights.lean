import Dubon2026.CommonCoefficientLocalField
import Dubon2026.CMSourceCoefficientProperties

/-! The source common coefficient field and its actual integral weights.
All original embeddings into the local algebraic closure land in the
constructed finite field. Its local structure and compatible valuation
are constructed, and the literal dominant integral induced tensor is
finite free, nonzero and continuously acted on by the original unitary
group. This is the coefficient-field and lattice obligation in BLGG
Section 3.2, not nonzero prescribed Hecke localization or automorphy.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField ValuativeRel

attribute [local instance] rationalPrimeLocalField_charZero

/-- The actual finite common local field supplies nonzero finite-free dominant source coefficients with continuous original arithmetic action, without a common-field, lattice or continuous-representation input. -/
theorem cmCommonCoefficientWeight_exists
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    (p : ℕ) (hp : p.Prime) (places : Set (HeightOneSpectrum (𝓞 K))) :
    let E := commonCoefficientField K (rationalPrimeLocalField p hp)
    ∃ (_ : UniformSpace E) (_ : ValuativeRel E) (_ : IsUniformAddGroup E)
      (_ : IsNonarchimedeanLocalField E)
      (_ : (ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
        (ValuativeRel.valuation E)),
      (∀ (tau : K →ₐ[ℚ] AlgebraicClosure (rationalPrimeLocalField p hp)) (x : K), tau x ∈ E) ∧
      CMSourceIntegralWeightProperties K E p hp places := by
  let E := commonCoefficientField K (rationalPrimeLocalField p hp)
  obtain ⟨u, v, hu, hl, he, _, ha⟩ :=
    commonCoefficientField_exists_local_structure K (rationalPrimeLocalField p hp)
  letI : UniformSpace E := u
  letI : ValuativeRel E := v
  letI : IsUniformAddGroup E := hu
  letI : IsNonarchimedeanLocalField E := hl
  letI : (ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation E) := he
  refine ⟨u, v, hu, hl, he, ha, ?_⟩
  exact cmSourceIntegralWeight_properties K E p hp places

end
end Dubon2026
