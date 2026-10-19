import Dubon2026.ArithmeticSupportRingFamily
import Dubon2026.ArithmeticFixedDeterminantCompactness
import Dubon2026.Reuse.Imperial.Patching.Utils.AdicTopology

/-! Actual coefficient-ring hypotheses for every member of the selected
arithmetic family. These are derived from the existing universal rings,
and permit the proved uniform bound to descend to genuine further local
deformation quotients when those conditions are constructed. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- Every actual enlarged-support ring is Noetherian with finite
residue field, compact Hausdorff and maximal-adic in its original topology. -/
theorem arithmeticSupportFamilyRing_localData
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ x, GeneralLinearGroup.det (σ x) = Units.map (algebraMap O (ResidueField O)) (δ x))
    (Q : ℕ → Finset Nat.Primes) (i : ℕ) :
    letI := arithmeticSupportFamilyRing_isLocal a ha q degree hqa σ hσ δ Q hδ i
    IsNoetherianRing (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q i) ∧
      Finite (ResidueField (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q i)) ∧
      CompactSpace (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q i) ∧
      T2Space (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q i) ∧
      IsAdicTopology (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q i) := by
  let b : 𝓞 ℚ := a * ∏ p ∈ Q i, (p.val : 𝓞 ℚ)
  let hb : b ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr
    (fun p _ => Nat.cast_ne_zero.mpr p.property.ne_zero))
  let hab : a ∣ b := dvd_mul_right a _
  let π := rationalArithmeticSupportRestriction a b hab
  let σb := σ.comp π.toMonoidHom
  let hσb : Continuous σb := hσ.comp π.continuous
  let δb := δ.comp π.toMonoidHom
  let hδb : ∀ x, GeneralLinearGroup.det (σb x) =
      Units.map (algebraMap O (ResidueField O)) (δb x) := fun x => hδ (π x)
  let hqb := dvd_trans hqa hab
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
  have hR := arithmeticFixedDeterminantRing_localData b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
  let eR := arithmeticFixedDeterminantResidueEquiv b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
  exact ⟨hR.1, Finite.of_equiv (ResidueField O) eR.symm.toEquiv,
    arithmeticFixedDeterminantRing_compactSpace b hb q (Fact.out : q.Prime) hqb σb hσb δb,
    arithmeticFixedDeterminantRing_t2Space b hb q (Fact.out : q.Prime) hqb σb hσb δb,
    ⟨hR.2.2⟩⟩

end
end Dubon2026
