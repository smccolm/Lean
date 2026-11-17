import Dubon2026.SourceOriginalTorusDetectingFamily
import Dubon2026.SourceOriginalArithmeticTorusPrimeProperty

/-! DUB-17/18 -> original dual-Selmer auxiliary families. Combine original
coefficient finiteness with the already proved original regular-prime theorem;
no supplied finite family or finite-dimensionality assumption remains. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix
open scoped NumberField

/-- Every original symmetric twisted H1 subspace has a dimension-bounded
jointly detecting family of genuine regular congruence primes. -/
def HasOriginalArithmeticTorusFamilies
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a)
    {F : Type} [Field F] [CharP F p] [TopologicalSpace F]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) F) : Prop :=
  ∀ (_ : DiscreteTopology F) (_ : IsTopologicalRing F) (hρ : Continuous ρ) (n level : ℕ),
    2 * n < p - 1 →
    let R := (homogeneousSymmetricGL n).comp ρ
    let hR := (homogeneousSymmetricGL_continuous n).comp hρ
    let ξ := rationalArithmeticCyclotomicCoefficientCharacter a p hpa F
    let A := matrixTraceZeroCharacterRep R ξ.toMonoidHom
    let hA := matrixTraceZeroCharacterAction_continuous R hR ξ.toMonoidHom ξ.continuous
    HasArithmeticTorusDetectingFamily a p n level A hA R hR

/-- Original regular-prime detection supplies the full bounded family on
every original H1 subspace; global finiteness is proved by scalar restriction. -/
theorem original_torus_prime_detection_gives_finite_families
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a)
    {F : Type} [Field F] [Finite F] [CharP F p] [TopologicalSpace F]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) F)
    (hprimes : HasOriginalArithmeticTorusPrimeDetection a p hpa ρ) :
    HasOriginalArithmeticTorusFamilies a p hpa ρ := by
  intro hDiscrete hRing hρ n level hn
  dsimp only
  exact rationalArithmetic_original_torus_detecting_family a ha p n level hpa
    _ _ _ _ (hprimes hDiscrete hRing hρ n level hn)

end
end Dubon2026.SourceDickson
