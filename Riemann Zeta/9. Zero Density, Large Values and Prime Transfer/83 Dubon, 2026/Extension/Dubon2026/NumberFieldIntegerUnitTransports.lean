import Dubon2026.NumberFieldLocalUnitTransports

/-! # Original transports on completion integer rings and their units

The already proved valuation identity restricts the original completed
field equivalence to the actual integer rings. Its unit transports and
coherence laws are derived, supplying the outside-support coefficients
in DUB-17's local-to-global idele cohomology calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
attribute [local instance] numberFieldGaloisPlaceAction

/-- The original completed field transport restricted to its original integer rings. -/
def numberFieldIntegerRingTransport (σ : Gal(L/K))
    (v w : HeightOneSpectrum (𝓞 L)) (h : σ • v = w) :
    v.adicCompletionIntegers L ≃+* w.adicCompletionIntegers L where
  toFun x := ⟨numberFieldGaloisLocalTransport K L σ v w h x.val, by
    change Valued.v (numberFieldGaloisLocalTransport K L σ v w h x.val) ≤ 1
    rw [numberFieldGaloisLocalTransport_valuation]
    exact x.property⟩
  invFun y := ⟨(numberFieldGaloisLocalTransport K L σ v w h).symm y.val, by
    have hv := numberFieldGaloisLocalTransport_valuation K L σ v w h
      ((numberFieldGaloisLocalTransport K L σ v w h).symm y.val)
    rw [RingEquiv.apply_symm_apply] at hv
    change Valued.v ((numberFieldGaloisLocalTransport K L σ v w h).symm y.val) ≤ 1
    rw [← hv]
    exact y.property⟩
  left_inv x := Subtype.ext ((numberFieldGaloisLocalTransport K L σ v w h).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((numberFieldGaloisLocalTransport K L σ v w h).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

/-- The original integer-unit transport as an integer-linear equivalence. -/
def numberFieldIntegerUnitTransport (σ : Gal(L/K))
    (v w : HeightOneSpectrum (𝓞 L)) (h : σ • v = w) :
    Additive (v.adicCompletionIntegers L)ˣ ≃ₗ[ℤ] Additive (w.adicCompletionIntegers L)ˣ :=
  (Units.mapEquiv (numberFieldIntegerRingTransport K L σ v w h).toMulEquiv).toAdditive.toIntLinearEquiv

/-- Integer-unit transport retains the original completed field value. -/
theorem numberFieldIntegerUnitTransport_val (σ : Gal(L/K))
    (v w : HeightOneSpectrum (𝓞 L)) (h : σ • v = w)
    (x : Additive (v.adicCompletionIntegers L)ˣ) :
    ((numberFieldIntegerUnitTransport K L σ v w h x).toMul.val : w.adicCompletion L) =
      numberFieldGaloisLocalTransport K L σ v w h x.toMul.val.val := rfl

/-- Identity fixes the actual original integer units. -/
theorem numberFieldIntegerUnitTransport_one (v : HeightOneSpectrum (𝓞 L))
    (x : Additive (v.adicCompletionIntegers L)ˣ) :
    numberFieldIntegerUnitTransport K L 1 v v (one_smul Gal(L/K) v) x = x := by
  apply Units.ext
  apply Subtype.ext
  exact numberFieldGaloisLocalTransport_one K L v x.toMul.val.val

/-- Original automorphism multiplication composes the actual integer-unit transports. -/
theorem numberFieldIntegerUnitTransport_mul (σ τ : Gal(L/K))
    (v u w : HeightOneSpectrum (𝓞 L)) (hτ : τ • v = u) (hσ : σ • u = w)
    (hστ : (σ * τ) • v = w) (x : Additive (v.adicCompletionIntegers L)ˣ) :
    numberFieldIntegerUnitTransport K L (σ * τ) v w hστ x =
      numberFieldIntegerUnitTransport K L σ u w hσ
        (numberFieldIntegerUnitTransport K L τ v u hτ x) := by
  apply Units.ext
  apply Subtype.ext
  exact numberFieldGaloisLocalTransport_mul K L σ τ v u w hτ hσ hστ x.toMul.val.val

end
end Dubon2026
