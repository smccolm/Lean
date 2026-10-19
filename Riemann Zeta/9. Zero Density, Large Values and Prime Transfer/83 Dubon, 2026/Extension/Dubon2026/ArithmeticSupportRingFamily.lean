import Dubon2026.ArithmeticFixedDeterminantRing
import Dubon2026.ArithmeticSupportRestriction

/-! The genuine enlarged-support universal rings indexed by auxiliary
levels. This names the actual ring family needed for the reused patching
algebra's uniform-rank hypothesis; each member is the existing arithmetic
fixed-determinant ring, with its support and residual representation. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
  (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
  (Q : ℕ → Finset Nat.Primes)

/-- The actual universal arithmetic ring at the support enlarged by
the selected prime family at a given level. -/
abbrev ArithmeticSupportFamilyRing (i : ℕ) :=
  let b : 𝓞 ℚ := a * ∏ p ∈ Q i, (p.val : 𝓞 ℚ)
  let hb : b ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr
    (fun p _ => Nat.cast_ne_zero.mpr p.property.ne_zero))
  let hab : a ∣ b := dvd_mul_right a _
  let π := rationalArithmeticSupportRestriction a b hab
  ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) (dvd_trans hqa hab)
    (σ.comp π.toMonoidHom) (hσ.comp π.continuous) (δ.comp π.toMonoidHom)

/-- The original determinant congruence makes every actual family
member local. No ring-locality certificate is supplied at any level. -/
theorem arithmeticSupportFamilyRing_isLocal
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (i : ℕ) : IsLocalRing (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q i) := by
  unfold ArithmeticSupportFamilyRing
  apply arithmeticFixedDeterminantRing_isLocal
  intro g
  exact hδ _

end
end Dubon2026
