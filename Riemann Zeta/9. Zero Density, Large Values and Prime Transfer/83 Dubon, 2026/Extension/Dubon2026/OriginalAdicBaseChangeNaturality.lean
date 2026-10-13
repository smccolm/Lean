import Dubon2026.OriginalAdicBaseChangeClosed

/-! # Naturality of original finite-completion base change

Original base-completion elements are compatible across all original
primes in a Galois orbit. This is the coordinate consistency needed for
DUB-17's original finite-adele fixed-point descent and native norm quotient.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain UniformSpace
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Original completed base change commutes with the actual Galois transport between primes. -/
theorem originalAdicBaseChangeMap_transport
    (v : HeightOneSpectrum (𝓞 K)) (u w : HeightOneSpectrum (𝓞 L))
    [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
    (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ u = w)
    (x : v.adicCompletion K) :
    numberFieldGaloisLocalTransport K L σ u w hσ (originalAdicBaseChangeMap K L v u x) =
      originalAdicBaseChangeMap K L v w x := by
  induction x using Completion.induction_on
  · exact isClosed_eq
      ((numberFieldGaloisLocalTransport_continuous K L σ u w hσ).comp
        (originalAdicBaseChangeMap_continuous K L v u))
      (originalAdicBaseChangeMap_continuous K L v w)
  · rename_i x
    change numberFieldGaloisLocalTransport K L σ u w hσ
      (originalAdicBaseChangeMap K L v u (algebraMap K (v.adicCompletion K) x.ofVal)) = _
    rw [originalAdicBaseChangeMap_algebraMap, numberFieldGaloisLocalTransport_algebraMap,
      σ.commutes]
    exact (originalAdicBaseChangeMap_algebraMap K L v w x.ofVal).symm

end
end Dubon2026
