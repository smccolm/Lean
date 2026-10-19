import Dubon2026.ArithmeticFixedDeterminantRepresentingComparison
import Dubon2026.ArithmeticUniversalOriginalSupportAlgebraicClassification

/-! The actual original-support ring comparison, with its genuine
residue maps and all original universal matrices retained in the
constructed output. Both inverse maps come from the proved arithmetic
classifications. No comparison certificate is supplied. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- The actual auxiliary inertia quotient and original-support framed
fixed-determinant ring are identified over the original coefficients,
with the original residue identification and every universal matrix. -/
def arithmeticUniversalOriginalSupportRingComparison
    {ι O : Type} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    [CharP (ResidueField O) q]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (b : 𝓞 ℚ) (hb : b ≠ 0) (Q : Finset Nat.Primes)
    (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ))
    (hab : a ∣ b) (haway : ∀ p : Q, ¬(p.val.val : 𝓞 ℚ) ∣ a) :=
  let π := rationalArithmeticSupportRestriction a b hab
  let σb := σ.comp π.toMonoidHom
  let hσb : Continuous σb := hσ.comp π.continuous
  let δb := δ.comp π.toMonoidHom
  let hqb := dvd_trans hqa hab
  let hδb : ∀ g, GeneralLinearGroup.det (σb g) =
      Units.map (algebraMap O (ResidueField O)) (δb g) := fun g => hδ (π g)
  let hIb : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      σb (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1 :=
    fun p g hg => rationalArithmeticSupportCharacter_inertia_eq_one a b hab σ
      p.val.val p.val.property (haway p) g hg
  let S := ArithmeticAuxiliaryUniversalRing b hb q hq hqb σb hσb δb Q
  letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σb hσb δb hδb Q hIb
  let hS := arithmeticAuxiliaryUniversalRing_localData b hb q hq hqb σb hσb δb hδb Q hIb
  letI := hS.1
  letI := hS.2.1
  letI : WithIdeal S := ⟨maximalIdeal S⟩
  let eS := arithmeticAuxiliaryUniversalResidueEquiv b hb q hq hqb σb hσb δb hδb Q hIb
  arithmeticFixedDeterminantRepresentingComparison (O := O) (S := S)
    rfl eS a ha q hq hqa σ hσ δ hδ b hab
    (arithmeticAuxiliaryUniversalRepresentation b hb q hq hqb σb hσb δb Q)
    (fun {A} _ _ _ _ _ _ hA eA =>
      arithmeticUniversalOriginalSupportAlgebraicClassification (O := O) (A := A)
        hA eA a b hb q hq hqb σ hσ δ hδ Q hba hab haway)

end
end Dubon2026
