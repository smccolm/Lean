import Dubon2026.ArithmeticRelativeNormalizedPrimeTotal

/-! # The local trace total comparison required for arbitrary local classes

This records equality of the canonical total and the local coordinate on
every genuine single-prime trace lift. It is a statement only; the actual
arithmetic theorem proves it from original base-prime support. DUB-17 uses
it to compare any supplied normalized local class with the constructed one.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The global total of every original single-prime trace lift equals its specified local coordinate; this proposition alone asserts no equality. -/
def OriginalLocalTraceTotalFormula
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (localInvariant : IsDedekindDomain.HeightOneSpectrum (𝓞 L) →
      groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ)) : Prop :=
    ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
      ∀ y : groupCohomology (originalAdicUnitRep K L w) 2,
        total (originalSinglePrimeIdeleH2Lift K L w y) =
          localInvariant w (originalSinglePrimeIdeleH2Lift K L w y)

end
end Dubon2026
