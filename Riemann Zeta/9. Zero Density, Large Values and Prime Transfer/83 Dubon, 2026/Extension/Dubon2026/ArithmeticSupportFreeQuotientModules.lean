import Dubon2026.ArithmeticSupportFreePatchingSystem
import Dubon2026.AuxiliaryParameterSurjectivity
import Dubon2026.FreeSurjectiveCoefficientRestriction

/-! The actual arithmetic actions are surjective. Consequently, nonzero free
auxiliary modules satisfy the exact quotient freeness and rank conditions used
by the patching theorem. The genuine Hecke modules, their freeness and their
uniform auxiliary ranks remain the explicit arithmetic obligations in DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators MvPowerSeries.WithPiTopology

variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree g : ℕ) [Fact q.Prime]
  (hqa : (q : 𝓞 ℚ) ∣ a) (eO : ResidueField O ≃+* ZMod q)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
  (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
  (hδ : ∀ x, GeneralLinearGroup.det (σ x) = Units.map (algebraMap O (ResidueField O)) (δ x))
  (Q : ℕ → Finset Nat.Primes)
  (hgood : ∀ i, ∀ p : Q i, RationalArithmeticTorusAuxiliaryPrime a q degree (i + 1)
    ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val)
  (hcard : ∀ i, (Q i).card = g)

/-- Original cyclic generators make each constructed arithmetic action
surjective onto its genuine auxiliary group algebra. -/
theorem arithmeticSupportFamilyParameterAction_surjective (i : ℕ) :
    Function.Surjective (arithmeticSupportFamilyParameterAction
      a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i) := by
  unfold arithmeticSupportFamilyParameterAction
  let b : 𝓞 ℚ := a * ∏ p ∈ Q i, (p.val : 𝓞 ℚ)
  have hb : b ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr
    (fun p _ => Nat.cast_ne_zero.mpr p.property.ne_zero))
  have hab : a ∣ b := dvd_mul_right a _
  let π := rationalArithmeticSupportRestriction a b hab
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) (dvd_trans hqa hab)
    (σ.comp π.toMonoidHom) (hσ.comp π.continuous) (δ.comp π.toMonoidHom) (fun x => hδ (π x))
  let c := arithmeticUniversalOriginalSupportConvergingParameterAction
    a ha b hb hab q degree (i + 1) hqa (Nat.succ_pos i) eO σ hσ δ hδ
    (Q i) rfl (hgood i) g (hcard i)
  change Function.Surjective c.action
  exact auxiliaryGroupAlgebra_parameter_surjective O (Q i) q c.comparison.index
    c.comparison.comparison.parameters.generators c.comparison.comparison.parameters.generates
    c.action c.variableValue

variable (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Nontrivial (M i)]
  [∀ i, Module (MonoidAlgebra O
    (∀ p : Q i, Fin degree → RationalPrimeTameCoefficientQuotient p.val.val q)) (M i)]
  [∀ i, Module.Free (MonoidAlgebra O
    (∀ p : Q i, Fin degree → RationalPrimeTameCoefficientQuotient p.val.val q)) (M i)]

/-- Actual auxiliary freeness transfers to the canonical annihilator quotient
for the constructed arithmetic action, with no quotient-freeness input. -/
theorem arithmeticSupportFamily_freeQuotientModule (i : ℕ) :
    let Λ := MvPowerSeries (Fin g × Fin degree) O
    letI : Module Λ (M i) := Module.compHom (M i) (arithmeticSupportFamilyParameterAction
      a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i)
    letI : Module (Λ ⧸ Module.annihilator Λ (M i)) (M i) :=
      Module.quotientAnnihilator (R := Λ) (M := M i)
    Module.Free (Λ ⧸ Module.annihilator Λ (M i)) (M i) := by
  let Λ := MvPowerSeries (Fin g × Fin degree) O
  letI : Module Λ (M i) := Module.compHom (M i) (arithmeticSupportFamilyParameterAction
    a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i)
  letI : Module (Λ ⧸ Module.annihilator Λ (M i)) (M i) :=
    Module.quotientAnnihilator (R := Λ) (M := M i)
  exact freeRestrictedModule_quotientAnnihilator (Λ := Λ)
    (B := MonoidAlgebra O (∀ p : Q i, Fin degree → RationalPrimeTameCoefficientQuotient p.val.val q))
    (M := M i)
    (arithmeticSupportFamilyParameterAction a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i)
    (arithmeticSupportFamilyParameterAction_surjective a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i)

/-- A bound on genuine auxiliary-module ranks gives the exact uniform-rank
class of the existing patching theorem for the constructed arithmetic actions. -/
theorem arithmeticSupportFamily_freeModules_uniformlyBoundedRank
    (n : ℕ) (hrank : ∀ i, Module.rank (MonoidAlgebra O
      (∀ p : Q i, Fin degree → RationalPrimeTameCoefficientQuotient p.val.val q)) (M i) < n) :
    let Λ := MvPowerSeries (Fin g × Fin degree) O
    letI : ∀ i, Module Λ (M i) := fun i => Module.compHom (M i) (arithmeticSupportFamilyParameterAction
      a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i)
    Module.UniformlyBoundedRank Λ M := by
  let Λ := MvPowerSeries (Fin g × Fin degree) O
  letI : ∀ i, Module Λ (M i) := fun i => Module.compHom (M i) (arithmeticSupportFamilyParameterAction
    a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i)
  refine ⟨n, fun i => ?_⟩
  rw [faithfulRestrictedModule_quotient_rank (Λ := Λ)
    (B := MonoidAlgebra O (∀ p : Q i, Fin degree → RationalPrimeTameCoefficientQuotient p.val.val q))
    (M := M i)
    (arithmeticSupportFamilyParameterAction a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i)
    (arithmeticSupportFamilyParameterAction_surjective a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i)]
  exact hrank i

end
end Dubon2026
