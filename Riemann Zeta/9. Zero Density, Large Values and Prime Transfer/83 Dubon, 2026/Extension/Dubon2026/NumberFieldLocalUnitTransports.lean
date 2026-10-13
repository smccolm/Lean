import Dubon2026.TransportedOrbitCoinduction
import Dubon2026.NumberFieldGaloisLocalTransport
import Dubon2026.NumberFieldGaloisArchimedeanCoherence
import Mathlib.Algebra.Group.Units.Equiv

/-! # Coherent transports on the original completion unit groups

The original finite and infinite completed field transports induce the
integer-linear unit transports required by the orbit/Shapiro comparison.
Both coherence laws are proved from the original completion maps, so
DUB-17's local idele factors use no assumed transport compatibility.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
attribute [local instance] numberFieldGaloisPlaceAction

/-- Original finite completion unit transport as an integer-linear equivalence. -/
def numberFieldFiniteUnitTransport (σ : Gal(L/K))
    (v w : HeightOneSpectrum (𝓞 L)) (h : σ • v = w) :
    Additive (v.adicCompletion L)ˣ ≃ₗ[ℤ] Additive (w.adicCompletion L)ˣ :=
  (Units.mapEquiv (numberFieldGaloisLocalTransport K L σ v w h).toMulEquiv).toAdditive.toIntLinearEquiv

/-- Identity transport fixes each original finite completion unit. -/
theorem numberFieldFiniteUnitTransport_one (v : HeightOneSpectrum (𝓞 L))
    (x : Additive (v.adicCompletion L)ˣ) :
    numberFieldFiniteUnitTransport K L 1 v v (one_smul Gal(L/K) v) x = x := by
  apply Units.ext
  exact numberFieldGaloisLocalTransport_one K L v x.toMul.val

/-- Multiplication of original automorphisms composes the actual finite unit transports. -/
theorem numberFieldFiniteUnitTransport_mul (σ τ : Gal(L/K))
    (v u w : HeightOneSpectrum (𝓞 L)) (hτ : τ • v = u) (hσ : σ • u = w)
    (hστ : (σ * τ) • v = w) (x : Additive (v.adicCompletion L)ˣ) :
    numberFieldFiniteUnitTransport K L (σ * τ) v w hστ x =
      numberFieldFiniteUnitTransport K L σ u w hσ
        (numberFieldFiniteUnitTransport K L τ v u hτ x) := by
  apply Units.ext
  exact numberFieldGaloisLocalTransport_mul K L σ τ v u w hτ hσ hστ x.toMul.val

/-- Original infinite completion unit transport as an integer-linear equivalence. -/
def numberFieldInfiniteUnitTransport (σ : Gal(L/K))
    (v w : InfinitePlace L) (h : σ • v = w) :
    Additive v.Completionˣ ≃ₗ[ℤ] Additive w.Completionˣ :=
  (Units.mapEquiv (numberFieldGaloisArchimedeanTransport K L σ v w h).toMulEquiv).toAdditive.toIntLinearEquiv

omit [NumberField L] in
/-- Identity transport fixes each original infinite completion unit. -/
theorem numberFieldInfiniteUnitTransport_one (v : InfinitePlace L)
    (x : Additive v.Completionˣ) :
    numberFieldInfiniteUnitTransport K L 1 v v (one_smul Gal(L/K) v) x = x := by
  apply Units.ext
  exact numberFieldGaloisArchimedeanTransport_one K L v x.toMul.val

omit [NumberField L] in
/-- Multiplication of original automorphisms composes the actual infinite unit transports. -/
theorem numberFieldInfiniteUnitTransport_mul (σ τ : Gal(L/K))
    (v u w : InfinitePlace L) (hτ : τ • v = u) (hσ : σ • u = w)
    (hστ : (σ * τ) • v = w) (x : Additive v.Completionˣ) :
    numberFieldInfiniteUnitTransport K L (σ * τ) v w hστ x =
      numberFieldInfiniteUnitTransport K L σ u w hσ
        (numberFieldInfiniteUnitTransport K L τ v u hτ x) := by
  apply Units.ext
  exact numberFieldGaloisArchimedeanTransport_mul K L σ τ v u w hτ hσ hστ x.toMul.val

end
end Dubon2026
