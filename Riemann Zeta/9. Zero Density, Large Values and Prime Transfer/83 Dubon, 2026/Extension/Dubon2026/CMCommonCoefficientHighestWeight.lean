import Dubon2026.CMCommonCoefficientAuxiliary
import Dubon2026.CMSourceHighestWeightProperties

/-! The constructed common field with the full original highest-weight coefficients.
The existing actual auxiliary comparison is retained, and its very same
coefficient tensor now has its proved irreducible highest-weight generic
fibres and exact original arithmetic action. Prescribed nonzero Hecke
localization, Galois realization and automorphy remain separate obligations.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ValuativeRel ComplexOrder

attribute [local instance] rationalPrimeLocalField_charZero

/-- The constructed adequate finite common local field supplies the original continuous finite-free highest-weight tensor, its exact equivariant generic fibre, and the original auxiliary module comparison, with all coefficient-identification assumptions discharged. -/
theorem cmCommonCoefficientHighestWeight_exists
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    (ell : ℕ) (hell : ell.Prime)
    (places : Set (HeightOneSpectrum (𝓞 K)))
    {S : Type} [Fintype S] (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (H : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ)
    (hpos : ∀ φ : K →+* ℂ, (φ.mapMatrix H.val).PosDef)
    (hv : ∀ s, v s ≠ cmFinitePlaceConjugation K (v s))
    (hlocal : ∀ s, cmFiniteAdelicFormIntegralAtConjugate K H (v s))
    (hsep : Pairwise fun s t => v s ≠ v t ∧ v s ≠ cmFinitePlaceConjugation K (v t))
    (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ s, w ≠ v s ∧ w ≠ cmFinitePlaceConjugation K (v s))
    (p : ℕ) (hp : p.Prime) [CharP (Valued.ResidueField (w.adicCompletion K)) p]
    (hlarge : Fintype.card (Fin (n + 1)) * Module.finrank ℚ K < p - 1) (q : ℕ) :
    let E := commonCoefficientField K (rationalPrimeLocalField ell hell)
    ∃ (_ : UniformSpace E) (_ : ValuativeRel E) (_ : IsUniformAddGroup E)
      (_ : IsNonarchimedeanLocalField E)
      (_ : (ValuativeRel.valuation (rationalPrimeLocalField ell hell)).HasExtension
        (ValuativeRel.valuation E)),
      (∀ (tau : K →ₐ[ℚ] AlgebraicClosure (rationalPrimeLocalField ell hell)) (x : K), tau x ∈ E) ∧
      CMSourceIntegralWeightProperties K E ell hell places ∧
      CMSourceHighestWeightProperties K E ell hell places ∧
      CMSourceAuxiliaryWeightProperties K E ell hell places v n H hpos hv hlocal hsep w hw p hp hlarge q := by
  let E := commonCoefficientField K (rationalPrimeLocalField ell hell)
  obtain ⟨u, val, hu, hl, he, ha, hweight, haux⟩ :=
    cmCommonCoefficientAuxiliary_exists K ell hell places v n H hpos hv hlocal hsep w hw p hp hlarge q
  letI : UniformSpace E := u
  letI : ValuativeRel E := val
  letI : IsUniformAddGroup E := hu
  letI : IsNonarchimedeanLocalField E := hl
  letI : (ValuativeRel.valuation (rationalPrimeLocalField ell hell)).HasExtension
      (ValuativeRel.valuation E) := he
  exact ⟨u, val, hu, hl, he, ha, hweight,
    cmSourceHighestWeight_properties K E ell hell places, haux⟩

end
end Dubon2026
