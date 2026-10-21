import Dubon2026.SourceDiagonalUnitPair
import Dubon2026.SourceOriginalCyclotomicLocal
import Dubon2026.ArithmeticCyclotomicCoefficientCharacter
import Mathlib.Topology.Algebra.Group.Units

/-! DUB-17/18 -> residual Galois association -> boundary Dirichlet pair.
The pair gives an actual continuous representation of the original
arithmetic Galois group. It factors through the existing finite cyclotomic
characters and retains their original local restriction.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
open Matrix

variable {F : Type} [Field F] (N p : ℕ) [CharP F p]

/-- The two given finite unit characters and the canonical characteristic
map define the actual finite diagonal representation. -/
def sourceBoundaryGaloisFiniteRepresentation
    (ψ₁ ψ₂ : (ZMod N)ˣ →* Fˣ) :
    ((ZMod N)ˣ × (ZMod p)ˣ) →* GeneralLinearGroup (Fin 2) F :=
  sourceDiagonalUnitPair
    (ψ₁.comp (MonoidHom.fst _ _))
    (((Units.map (ZMod.castHom (dvd_refl p) F).toMonoidHom).comp
      (MonoidHom.snd _ _)) * (ψ₂.comp (MonoidHom.fst _ _)))

/-- The original arithmetic Galois representation of the residual
Dirichlet pair, using the genuine finite cyclotomic characters. -/
def sourceBoundaryGaloisRepresentation
    (a : 𝓞 ℚ) [NeZero N] [NeZero p]
    (hNa : (N : 𝓞 ℚ) ∣ a) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ψ₁ ψ₂ : (ZMod N)ˣ →* Fˣ) :
    rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) F :=
  (sourceBoundaryGaloisFiniteRepresentation N p ψ₁ ψ₂).comp
    ((rationalArithmeticCyclotomicCharacter a N hNa).toMonoidHom.prod
      (rationalArithmeticCyclotomicCharacter a p hpa).toMonoidHom)

/-- Finite cyclotomic factorization proves continuity of the actual
matrix representation; no continuity premise on the finite characters is needed. -/
theorem sourceBoundaryGaloisRepresentation_continuous
    [TopologicalSpace F] (a : 𝓞 ℚ) [NeZero N] [NeZero p]
    (hNa : (N : 𝓞 ℚ) ∣ a) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ψ₁ ψ₂ : (ZMod N)ˣ →* Fˣ) :
    Continuous (sourceBoundaryGaloisRepresentation N p a hNa hpa ψ₁ ψ₂) := by
  have hf : Continuous (sourceBoundaryGaloisFiniteRepresentation N p ψ₁ ψ₂) :=
    continuous_of_discreteTopology
  exact hf.comp
    ((rationalArithmeticCyclotomicCharacter a N hNa).continuous.prodMk
      (rationalArithmeticCyclotomicCharacter a p hpa).continuous)

/-- The trace of the constructed arithmetic representation is exactly
the Dirichlet pair with the original cyclotomic twist. -/
theorem sourceBoundaryGaloisRepresentation_trace
    (a : 𝓞 ℚ) [NeZero N] [NeZero p]
    (hNa : (N : 𝓞 ℚ) ∣ a) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ψ₁ ψ₂ : (ZMod N)ˣ →* Fˣ) (g : rationalArithmeticGaloisGroup a) :
    Matrix.trace (sourceBoundaryGaloisRepresentation N p a hNa hpa ψ₁ ψ₂ g).val =
      (ψ₁ (rationalArithmeticCyclotomicCharacter a N hNa g) : F) +
      ZMod.castHom (dvd_refl p) F
        (rationalArithmeticCyclotomicCharacter a p hpa g : ZMod p) *
        (ψ₂ (rationalArithmeticCyclotomicCharacter a N hNa g) : F) := by
  change Matrix.trace (sourceDiagonalUnitPair _ _
    (rationalArithmeticCyclotomicCharacter a N hNa g,
      rationalArithmeticCyclotomicCharacter a p hpa g)).val = _
  rw [sourceDiagonalUnitPair_trace]
  rfl

/-- Product-one Dirichlet characters give the original cyclotomic
determinant on the entire arithmetic Galois group. -/
theorem sourceBoundaryGaloisRepresentation_det
    (a : 𝓞 ℚ) [NeZero N] [NeZero p]
    (hNa : (N : 𝓞 ℚ) ∣ a) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ψ₁ ψ₂ : (ZMod N)ˣ →* Fˣ)
    (hψ : ∀ u, (ψ₁ u : F) * (ψ₂ u : F) = 1)
    (g : rationalArithmeticGaloisGroup a) :
    Matrix.det (sourceBoundaryGaloisRepresentation N p a hNa hpa ψ₁ ψ₂ g).val =
      ZMod.castHom (dvd_refl p) F
        (rationalArithmeticCyclotomicCharacter a p hpa g : ZMod p) := by
  change Matrix.det (sourceDiagonalUnitPair _ _
    (rationalArithmeticCyclotomicCharacter a N hNa g,
      rationalArithmeticCyclotomicCharacter a p hpa g)).val = _
  rw [sourceDiagonalUnitPair_det]
  change (ψ₁ _ : F) * (ZMod.castHom (dvd_refl p) F
    (rationalArithmeticCyclotomicCharacter a p hpa g : ZMod p) * (ψ₂ _ : F)) = _
  rw [mul_left_comm, hψ, mul_one]

end
end Dubon2026
