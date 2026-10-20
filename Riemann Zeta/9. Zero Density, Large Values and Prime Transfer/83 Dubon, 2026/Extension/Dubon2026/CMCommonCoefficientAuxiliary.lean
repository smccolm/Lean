import Dubon2026.CMCommonCoefficientWeights
import Dubon2026.CMSourceAuxiliaryCoefficientProperties

/-! The constructed adequate common field in the actual source auxiliary comparison.
The exact source coefficient theorem is consumed together with the original
auxiliary module, its quotient group ring, unnormalized trace, unlocalized
nonzeroness and continuous arithmetic action. The remaining prescribed
Hecke/Galois realization and source automorphy are not inferred.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ValuativeRel ComplexOrder

attribute [local instance] rationalPrimeLocalField_charZero

/-- The constructed adequate finite common local field realizes the exact original auxiliary coefficient comparison, nonzero unlocalized forms and continuous source action, with no common-field or coefficient-representation input. -/
theorem cmCommonCoefficientAuxiliary_exists
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
    (hlarge : Fintype.card (Fin (n + 1)) * Module.finrank ℚ K < p - 1) (q : ℕ)
    :
    let E := commonCoefficientField K (rationalPrimeLocalField ell hell)
    ∃ (_ : UniformSpace E) (_ : ValuativeRel E) (_ : IsUniformAddGroup E)
      (_ : IsNonarchimedeanLocalField E)
      (_ : (ValuativeRel.valuation (rationalPrimeLocalField ell hell)).HasExtension
        (ValuativeRel.valuation E)),
      (∀ (tau : K →ₐ[ℚ] AlgebraicClosure (rationalPrimeLocalField ell hell)) (x : K), tau x ∈ E) ∧
      CMSourceIntegralWeightProperties K E ell hell places ∧
      CMSourceAuxiliaryWeightProperties K E ell hell places v n H hpos hv hlocal hsep w hw p hp hlarge q := by
  let E := commonCoefficientField K (rationalPrimeLocalField ell hell)
  obtain ⟨u, val, hu, hl, he, ha, hweight⟩ := cmCommonCoefficientWeight_exists K ell hell places
  letI : UniformSpace E := u
  letI : ValuativeRel E := val
  letI : IsUniformAddGroup E := hu
  letI : IsNonarchimedeanLocalField E := hl
  letI : (ValuativeRel.valuation (rationalPrimeLocalField ell hell)).HasExtension
      (ValuativeRel.valuation E) := he
  refine ⟨u, val, hu, hl, he, ha, hweight, ?_⟩
  exact cmSourceAuxiliaryWeight_properties K E ell hell places v n H hpos hv hlocal hsep w hw p hp hlarge q

end
end Dubon2026
