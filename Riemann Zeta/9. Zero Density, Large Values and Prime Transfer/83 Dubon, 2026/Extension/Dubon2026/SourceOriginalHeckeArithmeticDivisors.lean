import Dubon2026.SourceOriginalHeckeArithmeticPlaces
import Dubon2026.SourceOriginalHeckePicard
import Dubon2026.SourceOriginalArithmeticPicard

/-! DUB-17/18 -> original Tate Hecke realization -> arithmetic Hecke
equivariance. The proved restriction and ramification identities compare
actual divisor pullback and pushforward with the original place permutation.
The final original Hecke consumer supplies the field commutation identities
for its literal alpha and beta maps.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable {L : Type*} [Field L] [Algebra ℚ L]

theorem originalArithmeticDivisorEquiv_single (N : ℕ) (σ : L ≃ₐ[ℚ] L)
    (v : Place L (modularFunctionFieldOver N L)) (n : ℤ) :
    originalArithmeticDivisorEquiv N σ (Finsupp.single v n) =
      Finsupp.single (originalArithmeticPlace N σ v) n :=
  Finsupp.equivMapDomain_single _ _ _

variable [CharZero L] (N M : ℕ)
variable (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
variable (hφ : φ.toRingHom.Finite)
variable (hcomm : ∀ (σ : L ≃ₐ[ℚ] L) (x : modularFunctionFieldOver N L),
  originalArithmeticRingAut M σ (φ x) = φ (originalArithmeticRingAut N σ x))
include hcomm

theorem original_finitePullbackAlong_arithmetic (σ : L ≃ₐ[ℚ] L)
    (D : Divisor L (modularFunctionFieldOver N L)) :
    originalArithmeticDivisorEquiv M σ (Divisor.finitePullbackAlong φ hφ D) =
      Divisor.finitePullbackAlong φ hφ (originalArithmeticDivisorEquiv N σ D) := by
  ext w
  obtain ⟨v, rfl⟩ := (originalArithmeticPlaceEquiv M σ).surjective w
  change originalArithmeticDivisorEquiv M σ (Divisor.finitePullbackAlong φ hφ D)
    (originalArithmeticPlace M σ v) =
      Divisor.finitePullbackAlong φ hφ (originalArithmeticDivisorEquiv N σ D)
        (originalArithmeticPlace M σ v)
  rw [originalArithmeticDivisorEquiv_apply, Divisor.finitePullbackAlong_apply,
    Divisor.finitePullbackAlong_apply, originalArithmeticPlace_restrictAlong N M φ hφ hcomm,
    originalArithmeticDivisorEquiv_apply,
    originalArithmeticPlace_ramificationAlong N M φ hφ hcomm]

theorem original_geometricPushforwardAlong_arithmetic (σ : L ≃ₐ[ℚ] L)
    (D : Divisor L (modularFunctionFieldOver M L)) :
    Divisor.geometricPushforwardAlong φ hφ (originalArithmeticDivisorEquiv M σ D) =
      originalArithmeticDivisorEquiv N σ (Divisor.geometricPushforwardAlong φ hφ D) := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add w n D _ _ ih =>
    rw [map_add, map_add, map_add, map_add, ih]
    congr 1
    rw [originalArithmeticDivisorEquiv_single, Divisor.geometricPushforwardAlong_single,
      Divisor.geometricPushforwardAlong_single, originalArithmeticDivisorEquiv_single,
      originalArithmeticPlace_restrictAlong N M φ hφ hcomm]

end
end Dubon2026.SourceFunctionField
