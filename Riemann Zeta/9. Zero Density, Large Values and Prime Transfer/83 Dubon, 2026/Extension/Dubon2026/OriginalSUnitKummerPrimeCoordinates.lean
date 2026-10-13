import Dubon2026.PrimeExponentCoordinates
import Dubon2026.NumberFieldSUnitKummerRestriction

/-! # Coordinates on the actual prime-degree S-unit Kummer restriction kernel

The existing finite enlargement, original Kummer field and literal restriction
map already have the exact kernel order. Its proved Kummer exponent supplies
the residue-field coordinates without a coordinate hypothesis. Their number
is exactly the selected-prime count still required by DUB-17's class-index
calculation. Constructing the primes and their original S-unit localization
property remains a separate next obligation.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField IsMulCommutative
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- The actual enlarged S-unit Kummer restriction kernel has exactly s-1
prime-order coordinates for an original prime-degree Galois subextension. -/
theorem numberField_exists_prime_sUnit_kummer_coordinates
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K E = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (hE : E ≤ originalKummerRadicalField (Ω := Ω) p
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) p).range)),
      S₀ ⊆ S ∧
      let N := originalKummerRadicalField (Ω := Ω) p
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) p).range)
      letI : Algebra E N := (IntermediateField.inclusion hE).toAlgebra
      letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hE)
      let f : Gal(N/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
      Function.Surjective f ∧
        1 ≤ Fintype.card (NumberField.InfinitePlace K) + S.card ∧
        Nonempty (f.ker ≃* (Fin (Fintype.card (NumberField.InfinitePlace K) + S.card - 1) →
          Multiplicative (ZMod p))) := by
  have hp : p.Prime := Fact.out
  have hCard : Nat.card Gal(E/K) = p := (IsGalois.card_aut_eq_finrank K E).trans hDegree
  letI : IsCyclic Gal(E/K) := isCyclic_of_prime_card hCard
  letI : CommGroup Gal(E/K) := IsCyclic.commGroup
  have hPower (g : Gal(E/K)) : g ^ p = 1 := by
    rw [← hCard]
    exact pow_card_eq_one' (x := g)
  obtain ⟨S, hE, hS, hf, hCount, hKernel⟩ := numberField_exists_sUnit_kummer_restriction
    E p hp.one_lt ζ hζ hPower 1 (by simpa only [pow_one] using hCard) S₀
  refine ⟨S, hE, hS, ?_⟩
  let Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) p).range
  let N := originalKummerRadicalField (Ω := Ω) p Δ
  letI : Algebra E N := (IntermediateField.inclusion hE).toAlgebra
  letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hE)
  let f : Gal(N/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hroot : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  letI : IsMulCommutative Gal(N/K) := originalKummerRadicalField_galois_commutative p hroot Δ
  letI : CommGroup Gal(N/K) := inferInstance
  refine ⟨hf, hCount, ?_⟩
  apply primeExponent_exists_coordinates f.ker p _ _ hKernel
  intro g
  apply Subtype.ext
  exact originalKummerRadicalField_galois_pow_eq_one p hroot Δ g.val

end
end Dubon2026
