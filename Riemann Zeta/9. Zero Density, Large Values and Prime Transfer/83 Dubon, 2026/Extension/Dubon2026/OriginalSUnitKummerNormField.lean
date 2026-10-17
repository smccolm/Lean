import Dubon2026.OriginalFullSupportNormEquality
import Dubon2026.OriginalSUnitKummerUnramified
import Dubon2026.NumberFieldSUnitKummerDegree

/-! # The actual S-unit Kummer field has the required large-support norm subgroup

Consume the original radical field itself, deriving its finite dimension,
Galois structure, abelian prime-exponent group, exact degree and outside
unramifiedness. Only the normalized full-class system and the prescribed
large-support conditions remain explicit. The later reduction to the
original support is still required for DUB-17's invariant norm roots.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- The constructed full S-unit Kummer field has the literal required
norm subgroup once its normalized class system is supplied. No degree,
exponent, norm-index or upper-unramifiedness premise remains. -/
theorem originalSUnitKummer_normRange_eq_power_sup_outside
    (p : ℕ) [Fact p.Prime] (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
    (hClasses : Function.Surjective (numberFieldSupportedIdeleClassMap K S))
    (hBase : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Algebra.IsUnramifiedAt ℤ v.asIdeal)
    (hAway : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (p : 𝓞 K) ∉ v.asIdeal) :
    let N := OriginalSUnitKummerField K Ω S p
    letI : FiniteDimensional K N := numberField_sUnit_kummerField_finiteDimensional
      K Ω S S.finite_toSet p (Fact.out : p.Prime).pos
      ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩
    letI : NumberField N := NumberField.of_module_finite K N
    letI : IsGalois K N := originalKummerRadicalField_isGalois p _
    OriginalFiniteNormalizedClassSystem K N →
      LinearMap.range (originalIdeleClassNormLinear K N) =
        LinearMap.range ((p : ℤ) • (LinearMap.id :
          originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
        LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap := by
  have hp : p.Prime := Fact.out
  have hroot : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  let N := OriginalSUnitKummerField K Ω S p
  letI : FiniteDimensional K N :=
    numberField_sUnit_kummerField_finiteDimensional K Ω S S.finite_toSet p hp.pos hroot
  letI : NumberField N := NumberField.of_module_finite K N
  letI : IsGalois K N := originalKummerRadicalField_isGalois p _
  letI : IsMulCommutative Gal(N/K) := originalKummerRadicalField_galois_commutative p hroot _
  dsimp only
  intro hsys
  have hDegree : Module.finrank K N = p ^ (Fintype.card (InfinitePlace K) + S.card) := by
    simpa only [Set.ncard_coe_finset] using
      numberField_sUnit_kummerField_finrank K Ω S S.finite_toSet p hp.pos ζ hζ
  have hG : IsPGroup p Gal(N/K) :=
    IsPGroup.of_card ((IsGalois.card_aut_eq_finrank K N).trans hDegree)
  apply originalFullSupport_normRange_eq_power_sup_outside K N p hG hsys
    (originalKummerRadicalField_galois_pow_eq_one p hroot _) ζ hζ S hS
    hClasses hBase hAway _ hDegree
  intro w hw
  let v := originalFinitePrimeBelow K N w
  letI := originalFinitePrimeBelow_liesOver K N w
  exact originalSUnitKummer_unramified K Ω S p v w hw (hAway v hw) (hBase v hw)

end
end Dubon2026
