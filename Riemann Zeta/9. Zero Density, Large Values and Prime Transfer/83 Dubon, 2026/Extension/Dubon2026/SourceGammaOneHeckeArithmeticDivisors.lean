import Dubon2026.SourceGammaOneHeckeArithmeticPlaces
import Dubon2026.SourceGammaOneHeckePicard
import Dubon2026.SourceGammaOneArithmeticPicard

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> arithmetic equivariance of the actual Picard Hecke operator.
The proved place-restriction and ramification equations make actual divisor pullback and pushforward commute with coefficient action. The final Gamma1 consumer derives field commutation for both literal maps.
Reuse the existing original arithmetic correspondence proof on these actual
integral-ratio fields. No arithmetic naturality certificate is postulated. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve
variable {L : Type*} [Field L] [Algebra ℚ L]

theorem arithmeticDivisorEquiv_single (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (σ : L ≃ₐ[ℚ] L)
    (v : Place L (functionFieldOver Γ L)) (n : ℤ) :
    arithmeticDivisorEquiv Γ σ (Finsupp.single v n) =
      Finsupp.single (arithmeticPlace Γ σ v) n :=
  Finsupp.equivMapDomain_single _ _ _

variable [CharZero L] (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (φ : functionFieldOver Γ L →ₐ[L] functionFieldOver Δ L)
variable (hφ : φ.toRingHom.Finite)
variable (hcomm : ∀ (σ : L ≃ₐ[ℚ] L) (x : functionFieldOver Γ L),
  arithmeticRingAut Δ σ (φ x) = φ (arithmeticRingAut Γ σ x))
include hcomm

theorem finitePullbackAlong_arithmetic (σ : L ≃ₐ[ℚ] L)
    (D : Divisor L (functionFieldOver Γ L)) :
    arithmeticDivisorEquiv Δ σ (Divisor.finitePullbackAlong φ hφ D) =
      Divisor.finitePullbackAlong φ hφ (arithmeticDivisorEquiv Γ σ D) := by
  ext w
  obtain ⟨v, rfl⟩ := (arithmeticPlaceEquiv Δ σ).surjective w
  change arithmeticDivisorEquiv Δ σ (Divisor.finitePullbackAlong φ hφ D)
    (arithmeticPlace Δ σ v) =
      Divisor.finitePullbackAlong φ hφ (arithmeticDivisorEquiv Γ σ D)
        (arithmeticPlace Δ σ v)
  rw [arithmeticDivisorEquiv_apply, Divisor.finitePullbackAlong_apply,
    Divisor.finitePullbackAlong_apply, arithmeticPlace_restrictAlong Γ Δ φ hφ hcomm,
    arithmeticDivisorEquiv_apply,
    arithmeticPlace_ramificationAlong Γ Δ φ hφ hcomm]

theorem geometricPushforwardAlong_arithmetic (σ : L ≃ₐ[ℚ] L)
    (D : Divisor L (functionFieldOver Δ L)) :
    Divisor.geometricPushforwardAlong φ hφ (arithmeticDivisorEquiv Δ σ D) =
      arithmeticDivisorEquiv Γ σ (Divisor.geometricPushforwardAlong φ hφ D) := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add w n D _ _ ih =>
    rw [map_add, map_add, map_add, map_add, ih]
    congr 1
    rw [arithmeticDivisorEquiv_single, Divisor.geometricPushforwardAlong_single,
      Divisor.geometricPushforwardAlong_single, arithmeticDivisorEquiv_single,
      arithmeticPlace_restrictAlong Γ Δ φ hφ hcomm]

end
end Dubon2026.SourceFunctionField.GammaOne
