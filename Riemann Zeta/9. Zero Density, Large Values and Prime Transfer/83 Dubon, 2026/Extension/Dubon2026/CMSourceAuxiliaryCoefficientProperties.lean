import Dubon2026.CMSourceCoefficientProperties
import Dubon2026.CMSourceAutomorphicNontrivial

/-! Exact auxiliary properties of the original source coefficients.
The original arithmetic group, actual levels and true source tensor
are retained. The original comparison, unlocalized nonzeroness and
continuous restricted action are proved together. This is the actual
auxiliary-module dependency of BLGG potential automorphy for Theorem 2.6;
no prescribed nonzero Hecke localization is asserted.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ValuativeRel ComplexOrder

/-- The exact auxiliary finite-free and trace comparison, unlocalized nonzeroness and continuous original action for every dominant source weight. This statement is proved below. -/
def CMSourceAuxiliaryWeightProperties
    (K E : Type) [Field K] [NumberField K] [IsCMField K] [Field E] [CharZero E]
    (ell : ℕ) (hell : ell.Prime) [Algebra (rationalPrimeLocalField ell hell) E]
    [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation (rationalPrimeLocalField ell hell)).HasExtension (ValuativeRel.valuation E)]
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
    : Prop :=
  ∀ (lam : IntegralCoefficientEmbeddingIndex K E ell hell places → Fin (n + 1) → ℤ), (∀ i, Antitone (lam i)) →
    (CMPrimaryAuxiliaryComparisonStatement (R := 𝒪[E])
      (W := CMSourceIntegralWeight K E ell hell places n lam)
      v n H hpos hv hlocal hsep w hw p hp hlarge q
      (cmSourceSmallParabolicWeightRepresentation K E ell hell places v n H.val w lam)) ∧
    (let ρ := cmSourceSmallParabolicWeightRepresentation K E ell hell places v n H.val w lam
    let Γ := ((cmHermitianFiniteAdeleHom H.val).codRestrict (cmFiniteAdelicUnitaryGroup K H.val)
      (cmFiniteAdelicUnitaryGroup_principal K H.val)).range
    let U := cmFiniteAdelicSmallParabolicZero K v n H.val w
    let hH := cmHermitianPositiveUnit_star K H hpos
    let V := cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q
    let hVU := cmFiniteAdelicSmallPrimaryLevel_le K v n H hH hv hlocal hsep w hw q
    Nontrivial (algebraicAutomorphicForms (W := CMSourceIntegralWeight K E ell hell places n lam) Γ U ρ) ∧
      Nontrivial (algebraicAutomorphicForms (W := CMSourceIntegralWeight K E ell hell places n lam)
        Γ V (ρ.comp (V.inclusion hVU)))) ∧
    (letI : TopologicalSpace (CMSourceIntegralWeight K E ell hell places n lam) :=
      moduleTopology 𝒪[E] (CMSourceIntegralWeight K E ell hell places n lam)
    Continuous (fun x : cmFiniteAdelicSmallParabolicZero K v n H.val w ×
        CMSourceIntegralWeight K E ell hell places n lam =>
      cmSourceSmallParabolicWeightRepresentation K E ell hell places v n H.val w lam x.1 x.2))

/-- The actual source tensor satisfies the full auxiliary comparison, nonzeroness and continuous action, with all three conclusions derived from the original constructed objects. -/
theorem cmSourceAuxiliaryWeight_properties
    (K E : Type) [Field K] [NumberField K] [IsCMField K] [Field E] [CharZero E]
    (ell : ℕ) (hell : ell.Prime) [Algebra (rationalPrimeLocalField ell hell) E]
    [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation (rationalPrimeLocalField ell hell)).HasExtension (ValuativeRel.valuation E)]
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
    : CMSourceAuxiliaryWeightProperties K E ell hell places v n H hpos hv hlocal hsep w hw p hp hlarge q := by
  intro lam hlam
  refine ⟨cmSourceIntegralWeightAuxiliaryModule_comparison K E ell hell places v n H hpos hv hlocal hsep w hw p hp hlarge q lam,
    cmSourceIntegralWeightAutomorphic_nontrivial K E ell hell places v n H hpos hv hlocal hsep w hw p hp hlarge q lam hlam, ?_⟩
  letI : TopologicalSpace (CMSourceIntegralWeight K E ell hell places n lam) :=
    moduleTopology 𝒪[E] (CMSourceIntegralWeight K E ell hell places n lam)
  exact cmSourceSmallParabolicWeightRepresentation_continuous K E ell hell places v n H.val w lam

end
end Dubon2026
