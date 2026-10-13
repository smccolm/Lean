import Dubon2026.NumberFieldGaloisCompletionValuation

/-! # Coherent original local Galois transport

The maps are indexed by the actual source and target primes, with their
proved original permutation relation. Identity and composition hold on
the original completions, enabling the genuine finite-idele action.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain UniformSpace
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The original completed transport, with the actual target prime identified explicitly. -/
def numberFieldGaloisLocalTransport (σ : Gal(L/K))
    (v w : HeightOneSpectrum (𝓞 L)) (h : numberFieldGaloisPlaceEquiv K L σ v = w) :
    v.adicCompletion L ≃+* w.adicCompletion L := by
  subst w
  exact numberFieldGaloisCompletion K L σ v

/-- Reindexing the target leaves the original global-field action unchanged. -/
theorem numberFieldGaloisLocalTransport_algebraMap (σ : Gal(L/K))
    (v w : HeightOneSpectrum (𝓞 L)) (h : numberFieldGaloisPlaceEquiv K L σ v = w)
    (x : L) :
    numberFieldGaloisLocalTransport K L σ v w h (algebraMap L (v.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) (σ x) := by
  subst w
  exact numberFieldGaloisCompletion_algebraMap K L σ v x

/-- Original local transport is continuous for the original completed topologies. -/
theorem numberFieldGaloisLocalTransport_continuous (σ : Gal(L/K))
    (v w : HeightOneSpectrum (𝓞 L)) (h : numberFieldGaloisPlaceEquiv K L σ v = w) :
    Continuous (numberFieldGaloisLocalTransport K L σ v w h) := by
  subst w
  exact numberFieldGaloisCompletion_continuous K L σ v

/-- Original local transport preserves the original completed valuation. -/
theorem numberFieldGaloisLocalTransport_valuation (σ : Gal(L/K))
    (v w : HeightOneSpectrum (𝓞 L)) (h : numberFieldGaloisPlaceEquiv K L σ v = w)
    (x : v.adicCompletion L) :
    Valued.v (numberFieldGaloisLocalTransport K L σ v w h x) =
      (Valued.v x : WithZero (Multiplicative ℤ)) := by
  subst w
  exact numberFieldGaloisCompletion_valuation K L σ v x

/-- Identity transport is identity on the original completed field. -/
theorem numberFieldGaloisLocalTransport_one (v : HeightOneSpectrum (𝓞 L))
    (x : v.adicCompletion L) :
    numberFieldGaloisLocalTransport K L 1 v v (numberFieldGaloisPlaceEquiv_one K L v) x = x := by
  induction x using Completion.induction_on
  · exact isClosed_eq (numberFieldGaloisLocalTransport_continuous K L 1 v v _) continuous_id
  · rename_i x
    change numberFieldGaloisLocalTransport K L 1 v v _
      (algebraMap L (v.adicCompletion L) x.ofVal) = _
    rw [numberFieldGaloisLocalTransport_algebraMap]
    rfl

/-- Composition of actual global automorphisms composes the original completed transports. -/
theorem numberFieldGaloisLocalTransport_mul (σ τ : Gal(L/K))
    (v u w : HeightOneSpectrum (𝓞 L))
    (hτ : numberFieldGaloisPlaceEquiv K L τ v = u)
    (hσ : numberFieldGaloisPlaceEquiv K L σ u = w)
    (hστ : numberFieldGaloisPlaceEquiv K L (σ * τ) v = w)
    (x : v.adicCompletion L) :
    numberFieldGaloisLocalTransport K L (σ * τ) v w hστ x =
      numberFieldGaloisLocalTransport K L σ u w hσ
        (numberFieldGaloisLocalTransport K L τ v u hτ x) := by
  induction x using Completion.induction_on
  · exact isClosed_eq (numberFieldGaloisLocalTransport_continuous K L (σ * τ) v w hστ)
      ((numberFieldGaloisLocalTransport_continuous K L σ u w hσ).comp
        (numberFieldGaloisLocalTransport_continuous K L τ v u hτ))
  · rename_i x
    change numberFieldGaloisLocalTransport K L (σ * τ) v w hστ
      (algebraMap L (v.adicCompletion L) x.ofVal) =
        numberFieldGaloisLocalTransport K L σ u w hσ
          (numberFieldGaloisLocalTransport K L τ v u hτ
            (algebraMap L (v.adicCompletion L) x.ofVal))
    rw [numberFieldGaloisLocalTransport_algebraMap,
      numberFieldGaloisLocalTransport_algebraMap, numberFieldGaloisLocalTransport_algebraMap]
    rfl

end
end Dubon2026
