import Dubon2026.CMIntegralInducedTensorAction
import Dubon2026.CMFiniteAdelicSmallPrimaryAuxiliaryComparison

/-! Actual source integral weight in the original unitary auxiliary comparison.
The finite-free coefficient representation is no longer supplied. It is
the literal tensor of original integral Borel-induced regular functions,
acted on by original local unitary evaluation and the specified integral
coefficient embeddings. Its finite freeness is derived from the uniform
denominator and degree proof and the native tensor-product basis theorem.

CMSourceIntegralWeightComparison constructs the embedding family in a given
common coefficient field. Its required adequacy, source fields/forms/local
choices, dominant highest-weight and
nonzero localized Hecke realization, and automorphy remain unresolved.
This theorem does not close DUB-17 or DUB-18.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder BigOperators

/-- The exact original auxiliary finite-free and weighted-trace conclusion. This definition only names the full statement, and supplies no mathematical assumption. -/
def CMPrimaryAuxiliaryComparisonStatement
    {K : Type} {R W S : Type*} [Field K] [NumberField K] [IsCMField K]
    [CommRing R] [AddCommGroup W] [Module R W] [Fintype S]
    (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (H : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ)
    (hpos : ∀ φ : K →+* ℂ, (φ.mapMatrix H.val).PosDef)
    (hv : ∀ s, v s ≠ cmFinitePlaceConjugation K (v s))
    (hlocal : ∀ s, cmFiniteAdelicFormIntegralAtConjugate K H (v s))
    (hsep : Pairwise fun s t => v s ≠ v t ∧ v s ≠ cmFinitePlaceConjugation K (v t))
    (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ s, w ≠ v s ∧ w ≠ cmFinitePlaceConjugation K (v s))
    (p : ℕ) (hp : p.Prime) [CharP (Valued.ResidueField (w.adicCompletion K)) p]
    (hlarge : Fintype.card (Fin (n + 1)) * Module.finrank ℚ K < p - 1) (q : ℕ)
    (ρ : Representation R (cmFiniteAdelicSmallParabolicZero K v n H.val w) W)
    : Prop :=
    let hH := cmHermitianPositiveUnit_star K H hpos
    let U := cmFiniteAdelicSmallParabolicZero K v n H.val w
    let V := cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q
    let hVU := cmFiniteAdelicSmallPrimaryLevel_le K v n H hH hv hlocal hsep w hw q
    letI : Finite (U ⧸ V.subgroupOf U) :=
      cmFiniteAdelicSmallPrimaryQuotient_finite K v n H hH hv hlocal hsep w hw q
    letI : Fintype (U ⧸ V.subgroupOf U) := Fintype.ofFinite _
    let Γ := ((cmHermitianFiniteAdeleHom H.val).codRestrict (cmFiniteAdelicUnitaryGroup K H.val)
      (cmFiniteAdelicUnitaryGroup_principal K H.val)).range
    let hs := cmHermitianAdelic_smallLevel_of_large_congruence H.val hpos (cmFiniteAdelicUnitaryGroup K H.val)
      (cmFiniteAdelicUnitaryGroup_principal K H.val) U
      (cmFiniteAdelicSmallParabolicZero_isCompact K v n H.val w) w p hp hlarge
      (cmFiniteAdelicSmallParabolicZero_projection K v n H.val w)
    Module.Free (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hs).asModule ∧
    Module.Finite (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hs).asModule ∧
    ∃ e : (auxiliaryAutomorphicAction Γ U V hVU ρ hs).Coinvariants ≃ₗ[R]
        algebraicAutomorphicForms Γ U ρ,
      ∀ (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU)))
        (g : cmFiniteAdelicUnitaryGroup K H.val),
        (e (Representation.Coinvariants.mk
          (auxiliaryAutomorphicAction Γ U V hVU ρ hs) f)).val g =
          ∑ a : U ⧸ V.subgroupOf U, ρ a.out (f.val (g * (a.out : cmFiniteAdelicUnitaryGroup K H.val)))

/-- The existing auxiliary comparison proves the named full statement on the same objects. -/
theorem cmFiniteAdelicSmallPrimaryAuxiliaryStatement
    {K : Type} {R W S : Type*} [Field K] [NumberField K] [IsCMField K]
    [CommRing R] [AddCommGroup W] [Module R W] [Fintype S]
    (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (H : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ)
    (hpos : ∀ φ : K →+* ℂ, (φ.mapMatrix H.val).PosDef)
    (hv : ∀ s, v s ≠ cmFinitePlaceConjugation K (v s))
    (hlocal : ∀ s, cmFiniteAdelicFormIntegralAtConjugate K H (v s))
    (hsep : Pairwise fun s t => v s ≠ v t ∧ v s ≠ cmFinitePlaceConjugation K (v t))
    (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ s, w ≠ v s ∧ w ≠ cmFinitePlaceConjugation K (v s))
    (p : ℕ) (hp : p.Prime) [CharP (Valued.ResidueField (w.adicCompletion K)) p]
    (hlarge : Fintype.card (Fin (n + 1)) * Module.finrank ℚ K < p - 1) (q : ℕ)
    (ρ : Representation R (cmFiniteAdelicSmallParabolicZero K v n H.val w) W)
    [Module.Finite R W] [Module.Free R W] :
    CMPrimaryAuxiliaryComparisonStatement v n H hpos hv hlocal hsep w hw p hp hlarge q ρ :=
  cmFiniteAdelicSmallPrimaryAuxiliaryModule_comparison v n H hpos hv hlocal hsep w hw p hp hlarge q ρ

/-- The constructed original induced tensor coefficient representation satisfies the full auxiliary comparison, with finite freeness derived. -/
theorem cmFiniteAdelicIntegralWeightAuxiliaryModule_comparison
    {K : Type} {R I S : Type} [Field K] [NumberField K] [IsCMField K]
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [CharZero R]
    [Finite I] [Fintype S]
    (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (H : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ)
    (hpos : ∀ φ : K →+* ℂ, (φ.mapMatrix H.val).PosDef)
    (hv : ∀ s, v s ≠ cmFinitePlaceConjugation K (v s))
    (hlocal : ∀ s, cmFiniteAdelicFormIntegralAtConjugate K H (v s))
    (hsep : Pairwise fun s t => v s ≠ v t ∧ v s ≠ cmFinitePlaceConjugation K (v t))
    (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ s, w ≠ v s ∧ w ≠ cmFinitePlaceConjugation K (v s))
    (p : ℕ) (hp : p.Prime) [CharP (Valued.ResidueField (w.adicCompletion K)) p]
    (hlarge : Fintype.card (Fin (n + 1)) * Module.finrank ℚ K < p - 1) (q : ℕ)
    (c : I → HeightOneSpectrum (𝓞 K))
    (e : ∀ i, Valued.integer ((c i).adicCompletion K) →+* R)
    (lam : I → Fin (n + 1) → ℤ) :
    CMPrimaryAuxiliaryComparisonStatement (R := R)
      (W := IntegralInducedTensor R (n + 1) lam) v n H hpos hv hlocal hsep w hw p hp hlarge q
      (cmSmallParabolicInducedTensorRepresentation K R (I := I) c e v n H.val w lam) := by
  letI : Module.Finite R (IntegralInducedTensor R (n + 1) lam) :=
    integralLocalInducedTensorFinite R lam
  letI : Module.Free R (IntegralInducedTensor R (n + 1) lam) :=
    integralLocalInducedTensorFree R lam
  exact cmFiniteAdelicSmallPrimaryAuxiliaryStatement
    (R := R) (W := IntegralInducedTensor R (n + 1) lam) v n H hpos hv hlocal hsep
    w hw p hp hlarge q
    (cmSmallParabolicInducedTensorRepresentation K R (I := I) c e v n H.val w lam)

end
end Dubon2026
