import Dubon2026.ArithmeticConvergingParameterAction
import Dubon2026.FreeAuxiliaryModuleAnnihilator

/-! The exact arithmetic comparison supplies every action in the auxiliary
family. Its proved kernel bounds imply the existing patching-system condition
for nonzero free modules over the genuine auxiliary group algebras. These
modules, their Hecke interpretation and their freeness remain arithmetic inputs
on the DUB-17 potential-automorphy chain. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators MvPowerSeries.WithPiTopology

variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
  [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]

/-- The action at each level comes from the original arithmetic comparison,
including its proved factorization to the original deformation-ring action. -/
@[irreducible] def arithmeticSupportFamilyParameterAction
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree g : ℕ) [Fact q.Prime]
    (hqa : (q : 𝓞 ℚ) ∣ a) (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ x, GeneralLinearGroup.det (σ x) = Units.map (algebraMap O (ResidueField O)) (δ x))
    (Q : ℕ → Finset Nat.Primes)
    (hgood : ∀ i, ∀ p : Q i, RationalArithmeticTorusAuxiliaryPrime a q degree (i + 1)
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val)
    (hcard : ∀ i, (Q i).card = g) (i : ℕ) :
    @RingHom (MvPowerSeries (Fin g × Fin degree) O)
      (MonoidAlgebra O (∀ p : Q i, Fin degree → RationalPrimeTameCoefficientQuotient p.val.val q))
      (inferInstance : CommRing (MvPowerSeries (Fin g × Fin degree) O)).toNonAssocSemiring
      (inferInstance : CommRing (MonoidAlgebra O
        (∀ p : Q i, Fin degree → RationalPrimeTameCoefficientQuotient p.val.val q))).toNonAssocSemiring :=
  let b : 𝓞 ℚ := a * ∏ p ∈ Q i, (p.val : 𝓞 ℚ)
  let hb : b ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr
    (fun p _ => Nat.cast_ne_zero.mpr p.property.ne_zero))
  let hab : a ∣ b := dvd_mul_right a _
  let π := rationalArithmeticSupportRestriction a b hab
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) (dvd_trans hqa hab)
    (σ.comp π.toMonoidHom) (hσ.comp π.continuous) (δ.comp π.toMonoidHom) (fun x => hδ (π x))
  let c := arithmeticUniversalOriginalSupportConvergingParameterAction
    a ha b hb hab q degree (i + 1) hqa (Nat.succ_pos i) eO σ hσ δ hδ
    (Q i) rfl (hgood i) g (hcard i)
  { toFun := c.action
    map_zero' := c.action.map_zero
    map_one' := c.action.map_one
    map_add' := c.action.map_add
    map_mul' := c.action.map_mul }

/-- The actual family actions have quantitative kernel decay; this is derived
from the arithmetic congruences and original character generators. -/
theorem arithmeticSupportFamilyParameterAction_kernel_le
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree g : ℕ) [Fact q.Prime]
    (hqa : (q : 𝓞 ℚ) ∣ a) (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ x, GeneralLinearGroup.det (σ x) = Units.map (algebraMap O (ResidueField O)) (δ x))
    (Q : ℕ → Finset Nat.Primes)
    (hgood : ∀ i, ∀ p : Q i, RationalArithmeticTorusAuxiliaryPrime a q degree (i + 1)
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val)
    (hcard : ∀ i, (Q i).card = g) (i : ℕ) :
    RingHom.ker (arithmeticSupportFamilyParameterAction
      a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i) ≤
        maximalIdeal (MvPowerSeries (Fin g × Fin degree) O) ^ (i + 1) := by
  unfold arithmeticSupportFamilyParameterAction
  let b : 𝓞 ℚ := a * ∏ p ∈ Q i, (p.val : 𝓞 ℚ)
  have hb : b ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr
    (fun p _ => Nat.cast_ne_zero.mpr p.property.ne_zero))
  have hab : a ∣ b := dvd_mul_right a _
  let π := rationalArithmeticSupportRestriction a b hab
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) (dvd_trans hqa hab)
    (σ.comp π.toMonoidHom) (hσ.comp π.continuous) (δ.comp π.toMonoidHom) (fun x => hδ (π x))
  exact (arithmeticUniversalOriginalSupportConvergingParameterAction
    a ha b hb hab q degree (i + 1) hqa (Nat.succ_pos i) eO σ hσ δ hδ
    (Q i) rfl (hgood i) g (hcard i)).kernel_le (i + 1) le_rfl

/-- Nonzero freeness over the actual auxiliary algebras suffices for the exact
patching-system condition under the constructed arithmetic actions. No action
or annihilator convergence certificate is supplied as an input. -/
theorem arithmeticSupportFamily_freeModules_isPatchingSystem
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree g : ℕ) [Fact q.Prime]
    (hqa : (q : 𝓞 ℚ) ∣ a) (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ x, GeneralLinearGroup.det (σ x) = Units.map (algebraMap O (ResidueField O)) (δ x))
    (Q : ℕ → Finset Nat.Primes)
    (hgood : ∀ i, ∀ p : Q i, RationalArithmeticTorusAuxiliaryPrime a q degree (i + 1)
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val)
    (hcard : ∀ i, (Q i).card = g)
    (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Nontrivial (M i)]
    [∀ i, Module (MonoidAlgebra O
      (∀ p : Q i, Fin degree → RationalPrimeTameCoefficientQuotient p.val.val q)) (M i)]
    [∀ i, Module.Free (MonoidAlgebra O
      (∀ p : Q i, Fin degree → RationalPrimeTameCoefficientQuotient p.val.val q)) (M i)] :
    letI : ∀ i, Module (MvPowerSeries (Fin g × Fin degree) O) (M i) := fun i =>
      Module.compHom (M i) (arithmeticSupportFamilyParameterAction
        a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i)
    IsPatchingSystem (MvPowerSeries (Fin g × Fin degree) O) M Filter.atTop := by
  letI := finitePowerSeries_isAdicTopology (O := O) (η := Fin g × Fin degree)
  exact convergingParameterActions_freeModules_isPatchingSystem
    (MvPowerSeries (Fin g × Fin degree) O)
    (fun i => MonoidAlgebra O
      (∀ p : Q i, Fin degree → RationalPrimeTameCoefficientQuotient p.val.val q)) M
    (fun i => (arithmeticSupportFamilyParameterAction
      a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard i))
    (arithmeticSupportFamilyParameterAction_kernel_le
      a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard)

end
end Dubon2026
