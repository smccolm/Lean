import Dubon2026.CMSourceIntegralWeight
import Dubon2026.CMIntegralInducedAuxiliaryComparison

/-! Actual source embedding tensor in the unitary auxiliary comparison.
The coefficient ring is the original common local field's integer ring.
The index consists of actual number-field embeddings at the prescribed
places; their integral maps are constructed by completion and valuation
comparison. The coefficient representation and its finite freeness are
therefore derived. The conclusion is the complete original quotient-
group-ring freeness and the exact unnormalized weighted trace.

The prescribed source field/form/prime choices, dominant highest-weight
identification, nonzero localized Hecke/Galois realization and automorphy
are not supplied by this theorem; DUB-17 and DUB-18 remain open.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ValuativeRel ComplexOrder

/-- The actual source integral weight, constructed from the original field embeddings, satisfies the original auxiliary finite-free and exact-trace comparison without a supplied coefficient representation, finite-free lattice, integral embedding map or finite embedding-index certificate. -/
theorem cmSourceIntegralWeightAuxiliaryModule_comparison
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
    (lam : IntegralCoefficientEmbeddingIndex K E ell hell places → Fin (n + 1) → ℤ) :
    CMPrimaryAuxiliaryComparisonStatement (R := 𝒪[E])
      (W := CMSourceIntegralWeight K E ell hell places n lam)
      v n H hpos hv hlocal hsep w hw p hp hlarge q
      (cmSourceSmallParabolicWeightRepresentation K E ell hell places v n H.val w lam) := by
  exact cmFiniteAdelicIntegralWeightAuxiliaryModule_comparison
    (R := 𝒪[E]) (I := IntegralCoefficientEmbeddingIndex K E ell hell places)
    v n H hpos hv hlocal hsep w hw p hp hlarge q
    (fun i => integralCoefficientEmbeddingPrime K E ell hell i.val)
    (fun i => integralCoefficientEmbedding K E ell hell i.val) lam

end
end Dubon2026
