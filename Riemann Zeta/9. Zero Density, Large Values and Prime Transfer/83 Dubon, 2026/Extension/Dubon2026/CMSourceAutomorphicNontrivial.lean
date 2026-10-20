import Dubon2026.IntegralDominantTensorNontrivial
import Dubon2026.SmallLevelAutomorphicNontrivial
import Dubon2026.CMSourceIntegralWeightComparison

/-! The original source weight gives nonzero actual upper and lower
auxiliary automorphic forms. Coefficient nonzeroness comes from explicit
dominant regular-function vectors, not a supplied nonzero representation.
Arithmetic smallness and the actual unitary levels are the existing source
constructions. Prescribed Hecke localization remains a separate obligation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ValuativeRel ComplexOrder

/-- The original dominant embedding-tensor weight gives nonzero actual upper and lower primary auxiliary automorphic modules; no nonzero coefficient or automorphic-form witness is supplied. -/
theorem cmSourceIntegralWeightAutomorphic_nontrivial
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
    (lam : IntegralCoefficientEmbeddingIndex K E ell hell places → Fin (n + 1) → ℤ)
    (hlam : ∀ i, Antitone (lam i)) :
    let ρ := cmSourceSmallParabolicWeightRepresentation K E ell hell places v n H.val w lam
    let Γ := ((cmHermitianFiniteAdeleHom H.val).codRestrict (cmFiniteAdelicUnitaryGroup K H.val)
      (cmFiniteAdelicUnitaryGroup_principal K H.val)).range
    let U := cmFiniteAdelicSmallParabolicZero K v n H.val w
    let hH := cmHermitianPositiveUnit_star K H hpos
    let V := cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q
    let hVU := cmFiniteAdelicSmallPrimaryLevel_le K v n H hH hv hlocal hsep w hw q
    Nontrivial (algebraicAutomorphicForms (W := CMSourceIntegralWeight K E ell hell places n lam) Γ U ρ) ∧
      Nontrivial (algebraicAutomorphicForms (W := CMSourceIntegralWeight K E ell hell places n lam)
        Γ V (ρ.comp (V.inclusion hVU))) := by
  letI : Nontrivial (CMSourceIntegralWeight K E ell hell places n lam) :=
    cmSourceIntegralWeight_nontrivial K E ell hell places n lam hlam
  let ρ := cmSourceSmallParabolicWeightRepresentation K E ell hell places v n H.val w lam
  let Γ := ((cmHermitianFiniteAdeleHom H.val).codRestrict (cmFiniteAdelicUnitaryGroup K H.val)
    (cmFiniteAdelicUnitaryGroup_principal K H.val)).range
  let U := cmFiniteAdelicSmallParabolicZero K v n H.val w
  let hH := cmHermitianPositiveUnit_star K H hpos
  let V := cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q
  let hVU := cmFiniteAdelicSmallPrimaryLevel_le K v n H hH hv hlocal hsep w hw q
  have hs : ∀ (s : cmFiniteAdelicUnitaryGroup K H.val) (u : U),
      s * u * s⁻¹ ∈ Γ → u = 1 :=
    cmHermitianAdelic_smallLevel_of_large_congruence H.val hpos (cmFiniteAdelicUnitaryGroup K H.val)
      (cmFiniteAdelicUnitaryGroup_principal K H.val) U
      (cmFiniteAdelicSmallParabolicZero_isCompact K v n H.val w) w p hp hlarge
      (cmFiniteAdelicSmallParabolicZero_projection K v n H.val w)
  exact ⟨smallLevelAutomorphic_nontrivial Γ U ρ hs,
    smallLevelAuxiliary_nontrivial Γ U V hVU ρ hs⟩

end
end Dubon2026
