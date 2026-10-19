import Dubon2026.ArithmeticSupportFamilyLocalData
import Dubon2026.ArithmeticSupportUniformRank
import Dubon2026.LocalQuotientUniformRankDescent

/-! The actual uniform arithmetic ring bound survives genuine further
local deformation quotients. The quotient maps remain explicit until
the source-specific local conditions are constructed; no uniform bound
or coefficient-ring finiteness is assumed at that interface. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

/-- Derive uniform rank for any actual surjective local quotients of
the same enlarged-support arithmetic family. The source-ring topology,
Noetherianity, finite residue fields and uniform rank are all constructed. -/
theorem arithmeticSupportFamily_quotient_uniformlyBoundedRank
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
    (hcard : ∀ i, (Q i).card = g)
    (S : ℕ → Type) [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    (f : ∀ i, ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q i →+* S i)
    (hf : ∀ i, Function.Surjective (f i)) :
    Algebra.UniformlyBoundedRank S := by
  let R := ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q
  letI : ∀ i, IsLocalRing (R i) :=
    fun i => arithmeticSupportFamilyRing_isLocal a ha q degree hqa σ hσ δ Q hδ i
  letI : ∀ i, IsNoetherianRing (R i) :=
    fun i => (arithmeticSupportFamilyRing_localData a ha q degree hqa σ hσ δ hδ Q i).1
  letI : ∀ i, Finite (ResidueField (R i)) :=
    fun i => (arithmeticSupportFamilyRing_localData a ha q degree hqa σ hσ δ hδ Q i).2.1
  letI : Algebra.UniformlyBoundedRank R :=
    arithmeticSupportFamily_uniformlyBoundedRank a ha q degree g hqa eO σ hσ δ hδ Q hgood hcard
  exact localQuotientFamily_uniformlyBoundedRank R S f hf

end
end Dubon2026
