import Dubon2026.ArithmeticSupportRingFamily
import Dubon2026.ArithmeticUniversalBoundedPatchingRing
import Dubon2026.Reuse.Imperial.Patching.Algebra

/-! The actual enlarged-support arithmetic rings satisfy the existing
patching algebra's uniform-rank condition. The bound is derived from
their constructed common-parameter quotients over the original base
ring, not supplied as a separate arithmetic hypothesis. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- A family of genuine good auxiliary prime sets of fixed cardinality
gives the actual uniform arithmetic ring-rank bound required by patching. -/
theorem arithmeticSupportFamily_uniformlyBoundedRank
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree g : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ x, GeneralLinearGroup.det (σ x) = Units.map (algebraMap O (ResidueField O)) (δ x))
    (Q : ℕ → Finset Nat.Primes)
    (hgood : ∀ i, ∀ p : Q i, RationalArithmeticTorusAuxiliaryPrime a q degree (i + 1)
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val)
    (hcard : ∀ i, (Q i).card = g) :
    letI : ∀ i, IsLocalRing (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q i) :=
      fun i => arithmeticSupportFamilyRing_isLocal a ha q degree hqa σ hσ δ Q hδ i
    Algebra.UniformlyBoundedRank (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q) := by
  letI : ∀ i, IsLocalRing (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q i) :=
    fun i => arithmeticSupportFamilyRing_isLocal a ha q degree hqa σ hσ δ Q hδ i
  let A := ArithmeticFixedDeterminantRing a ha q (Fact.out : q.Prime) hqa σ hσ δ
  letI := arithmeticFixedDeterminantRing_isLocal a ha q (Fact.out : q.Prime) hqa σ hσ δ hδ
  letI := (arithmeticFixedDeterminantRing_localData a ha q (Fact.out : q.Prime) hqa σ hσ δ hδ).1
  constructor
  intro k
  refine ⟨Nat.card (ResidueField O) ^
    (∑ j ∈ Finset.range k, (Fintype.card (Fin g × Fin degree) + (localMaximalGenerators A).card) ^ j) + 1, ?_⟩
  intro i
  let b : 𝓞 ℚ := a * ∏ p ∈ Q i, (p.val : 𝓞 ℚ)
  have hb : b ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr
    (fun p _ => Nat.cast_ne_zero.mpr p.property.ne_zero))
  have hab : a ∣ b := dvd_mul_right a _
  let d := arithmeticUniversalOriginalSupportBoundedPatchingRingComparison
    a ha b hb hab q degree (i + 1) hqa (Nat.succ_pos i) eO σ hσ δ hδ
    (Q i) rfl (hgood i) g (hcard i)
  exact (d.property.2.2.2.2.2.2 k).trans_lt (Nat.lt_succ_self _)

end
end Dubon2026
