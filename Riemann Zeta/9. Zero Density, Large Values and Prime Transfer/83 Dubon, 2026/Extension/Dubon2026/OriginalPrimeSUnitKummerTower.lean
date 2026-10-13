import Dubon2026.OriginalPrimeSUnitKummerEmbedding
import Dubon2026.NumberFieldSUnitKummerDegree
import Dubon2026.PrimeExponentCoordinates

/-! # Original prime-degree restriction coordinates without changing fields

The actual embedding of the original upper field gives its literal
restriction map from the S-unit Kummer Galois group. The existing Kummer
degree and prime exponent compute its exact kernel coordinates. These are
the only replacement needed in selected-prime assembly to retain the
original arbitrary field's prime space and class norm in DUB-17's norm
index, avoiding general adelic isomorphism transport.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField Classical IsMulCommutative
variable (K L Ω : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- The literal original upper field has the required restriction-kernel
coordinates in one constructed original S-unit Kummer extension. -/
theorem original_primeDegree_sUnit_kummer_tower_coordinates
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (j : L →ₐ[K] OriginalSUnitKummerField K Ω S p), S₀ ⊆ S ∧
      let N := OriginalSUnitKummerField K Ω S p
      letI : Algebra L N := j.toAlgebra
      letI : IsScalarTower K L N := IsScalarTower.of_algHom j
      let f : Gal(N/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
      Function.Surjective f ∧
        1 ≤ Fintype.card (NumberField.InfinitePlace K) + S.card ∧
        Nonempty (f.ker ≃* (Fin (Fintype.card (NumberField.InfinitePlace K) + S.card - 1) →
          Multiplicative (ZMod p))) := by
  have hp : p.Prime := Fact.out
  have hroot : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  obtain ⟨S, hS, ⟨j⟩⟩ := original_primeDegree_sUnit_kummer_embedding K L Ω p hDegree ζ hζ S₀
  refine ⟨S, j, hS, ?_⟩
  let N := OriginalSUnitKummerField K Ω S p
  letI : Algebra L N := j.toAlgebra
  letI : IsScalarTower K L N := IsScalarTower.of_algHom j
  letI : IsGalois K N := originalKummerRadicalField_isGalois p _
  letI : FiniteDimensional K N :=
    numberField_sUnit_kummerField_finiteDimensional K Ω S S.finite_toSet p hp.pos hroot
  letI : IsMulCommutative Gal(N/K) := originalKummerRadicalField_galois_commutative p hroot _
  letI : CommGroup Gal(N/K) := inferInstance
  let f : Gal(N/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  have hf : Function.Surjective f := AlgEquiv.restrictNormalHom_surjective N
  have hL : Nat.card Gal(L/K) = p := (IsGalois.card_aut_eq_finrank K L).trans hDegree
  have hN : Nat.card Gal(N/K) = p ^ (Fintype.card (NumberField.InfinitePlace K) + S.card) := by
    simpa only [Set.ncard_coe_finset] using
      numberField_sUnit_kummerField_galois_card K Ω S S.finite_toSet p hp.pos ζ hζ
  have hr : 1 ≤ Fintype.card (NumberField.InfinitePlace K) + S.card := by
    have hle := Nat.card_le_card_of_surjective f hf
    have hle' : p ^ 1 ≤ p ^ (Fintype.card (NumberField.InfinitePlace K) + S.card) := by
      simpa only [hL, hN, pow_one] using hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle'
  have hQuot : Nat.card (Gal(N/K) ⧸ f.ker) = p :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).trans hL
  have hFactor : p ^ (Fintype.card (NumberField.InfinitePlace K) + S.card) = p * Nat.card f.ker := by
    rw [← hN, ← hQuot]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hKernel : Nat.card f.ker = p ^ (Fintype.card (NumberField.InfinitePlace K) + S.card - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    rw [← hFactor, mul_comm p, ← pow_succ, Nat.sub_add_cancel hr]
  refine ⟨hf, hr, ?_⟩
  apply primeExponent_exists_coordinates f.ker p _ _ hKernel
  intro g
  apply Subtype.ext
  exact originalKummerRadicalField_galois_pow_eq_one p hroot _ g.val

end
end Dubon2026
