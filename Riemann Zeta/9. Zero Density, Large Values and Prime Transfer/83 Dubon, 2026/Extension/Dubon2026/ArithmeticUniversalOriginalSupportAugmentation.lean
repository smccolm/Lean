import Dubon2026.ArithmeticUniversalAugmentationQuotient
import Dubon2026.ArithmeticUniversalOriginalSupportRingComparison
import Dubon2026.ArithmeticAuxiliaryAugmentationRepresentation

/-! The actual auxiliary family augmentation recovers the original
fixed-determinant framed ring and all original universal matrices.
This assembles the character quotient, arithmetic support descent and
the two actual universal-ring maps. Further local deformation conditions
and arithmetic Hecke, patching and automorphy inputs remain separate. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- The actual selected degree-parameter character family has an
augmentation quotient isomorphic to the genuine original-support
fixed-determinant framed ring. Every universal matrix agrees under
arithmetic restriction. All auxiliary inertia and residue compatibility
conditions are derived from the original support and selected primes. -/
def arithmeticUniversalOriginalSupportAugmentationComparison
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (b : 𝓞 ℚ) (hb : b ≠ 0) (hab : a ∣ b)
    (q degree level : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (hlevel : 0 < level) (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (Q : Finset Nat.Primes) (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ))
    (hgood : ∀ p : Q, RationalArithmeticTorusAuxiliaryPrime a q degree level
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val) :=
  let π := rationalArithmeticSupportRestriction a b hab
  let σb := σ.comp π.toMonoidHom
  let hσb : Continuous σb := hσ.comp π.continuous
  let δb := δ.comp π.toMonoidHom
  let hδb : ∀ g, GeneralLinearGroup.det (σb g) =
      Units.map (algebraMap O (ResidueField O)) (δb g) := fun g => hδ (π g)
  let hqb := dvd_trans hqa hab
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
  letI : CharP (ResidueField O) q :=
    charP_of_injective_ringHom (f := eO.symm.toRingHom) eO.symm.injective q
  let haway : ∀ p : Q, ¬(p.val.val : 𝓞 ℚ) ∣ a := fun p => (hgood p).1
  let hpb : ∀ p : Q, (p.val.val : 𝓞 ℚ) ∣ b := by
    intro p
    rw [hba]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun t : Nat.Primes => (t.val : 𝓞 ℚ)) p.property) a
  let d := Classical.choice (arithmeticUniversal_original_support_augmentation_quotient
    a b hab hb q degree level hqb hlevel eO σ hσ δ hδ Q hgood hpb)
  letI := arithmeticFixedDeterminantRing_isLocal a ha q (Fact.out : q.Prime) hqa σ hσ δ hδ
  let hIb : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      σb (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1 :=
    fun p g hg => rationalArithmeticSupportCharacter_inertia_eq_one a b hab σ
      p.val.val p.val.property (haway p) g hg
  letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q (Fact.out : q.Prime) hqb
    σb hσb δb hδb Q hIb
  let c := arithmeticUniversalOriginalSupportRingComparison a ha q (Fact.out : q.Prime) hqa
    σ hσ δ hδ b hb Q hba hab haway
  arithmeticAuxiliaryAugmentationRepresentationComparison
    (ι := Fin degree) b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb Q
    (fun p : Q => RationalPrimeTameCoefficientQuotient p.val.val q)
    (fun g => arithmeticFixedDeterminantRepresentation a ha q (Fact.out : q.Prime) hqa σ hσ δ (π g))
    c.equiv c.evaluation d

end
end Dubon2026
