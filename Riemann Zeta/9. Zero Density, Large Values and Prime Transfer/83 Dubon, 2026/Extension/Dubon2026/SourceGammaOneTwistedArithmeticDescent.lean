import Dubon2026.SourceGammaOneTwistedNormInertia
import Dubon2026.SourceGammaOneTwistedContinuity
import Dubon2026.SourceAbsoluteArithmeticDescent
import Dubon2026.Reuse.Imperial.Deformations.Lemmas

/-! DUB-17/18 -> original all-weight arithmetic association -> prescribed
arithmetic descent of the genuine finite homogeneous-valued Tate action.
Reuse the existing continuous unit lift and original unramified descent.
The exact local valuation and inertia consumer derive the ramification
input from two separate original geometric equalities. No arithmetic
quotient factorization, continuous action, or inertia identity is assumed.
The original degree/genus equalities and character realization remain. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup IntermediateField
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

private theorem monoid_arithmetic_descent {B : Type} [Monoid B]
    (a : ℕ) (ρ : Gal(Qbar/ℚ) →* B) (hc : @Continuous _ _ _ ⊥ ρ.toFun)
    (hI : ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ a →
      ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
        (g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
        g ∈ rationalPrimeNormInertia q hq → ρ (embeddedNormalGaloisRestriction e g) = 1) :
    letI : TopologicalSpace B := ⊥
    ∃ η : rationalArithmeticGaloisGroup (a : 𝓞 ℚ) →ₜ* Bˣ,
      ∀ σ, (η (sourceAbsoluteArithmeticRestriction (a : 𝓞 ℚ) σ) : B) = ρ σ := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  let χ : Gal(Qbar/ℚ) →ₜ* B := ⟨ρ, hc⟩
  obtain ⟨η, hη⟩ := absolute_continuous_normInertia_arithmetic_descent a χ.toHomUnits
    (fun q hq hqa e g hg => Units.ext (hI q hq hqa e g hg))
  exact ⟨η, fun σ => congrArg Units.val (hη σ)⟩

variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "Γ" => Gamma1 M
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver Γ Qbar))
attribute [local instance] specializationResidueAlgebra
private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V

theorem binaryArithmeticTateGaloisRep_arithmetic_descent_of_degree_genus_eq
    (hdeg : ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
      ∀ e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq,
        Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ (functionFieldOver Γ Qbar) =
          Module.finrank
            (IntermediateField.adjoin (IsLocalRing.ResidueField (sourceRationalLocalValuation q hq e))
              {residueJCoordinate (sourceRationalLocalValuation q hq e) Γ})
            (residueImage (sourceRationalLocalValuation q hq e) Γ))
    (hgen : ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
      ∀ e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq,
        genusFF (IsLocalRing.ResidueField (sourceRationalLocalValuation q hq e))
          (residueImage (sourceRationalLocalValuation q hq e) Γ) =
            genusFF Qbar (functionFieldOver Γ Qbar)) :
    let B := Module.End (ZMod N) (T →ₗ[ℤ_[p]] V)
    letI : TopologicalSpace B := ⊥
    ∃ η : rationalArithmeticGaloisGroup ((Q * p : ℕ) : 𝓞 ℚ) →ₜ* Bˣ,
      ∀ σ, (η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ) σ)).val =
        binaryArithmeticTateGaloisRep Q p n w σ := by
  apply monoid_arithmetic_descent (Q * p) (binaryArithmeticTateGaloisRep Q p n w)
    (binaryArithmeticTateGaloisRep_continuous Q p n w)
  intro q hq hqp e g hg
  have hs := binaryArithmeticTateGaloisRep_normInertia_of_degree_genus_eq Q p n w q hq hqp e
  have h1 := hs (hdeg q hq hqp e)
  have h2 := h1 (hgen q hq hqp e)
  exact h2 g hg

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
