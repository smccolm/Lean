import Dubon2026.GaloisTowerKernelCohomology
import Dubon2026.GaloisUnitInvariantBaseDescent

/-! # Original middle-field units are the actual restriction-kernel invariants -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]

/-- The actual restriction quotient is the original middle-field Galois
group by genuine surjectivity of automorphism restriction. -/
def galoisTowerQuotientEquiv :
    Gal(M/K) ⧸ (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker ≃* Gal(L/K) :=
  QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom L)
    (AlgEquiv.restrictNormalHom_surjective M)

/-- The original middle-field unit inclusion lands in the actual kernel
invariants and intertwines the original quotient action. -/
def galoisTowerQuotientUnitInclusion :
    Rep.res (galoisTowerQuotientEquiv K L M).toMonoidHom (Rep.ofAlgebraAutOnUnits K L) ⟶
      (Rep.ofAlgebraAutOnUnits K M).quotientToInvariants
        (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker :=
  Rep.ofHom ⟨((Units.map (algebraMap L M).toMonoidHom).toAdditive.toIntLinearMap).codRestrict
    _ (by
      intro u s
      change s.val • Units.map (algebraMap L M).toMonoidHom u.toMul =
        Units.map (algebraMap L M).toMonoidHom u.toMul
      apply Units.ext
      exact (galoisTowerKernelEquiv K L M s).commutes u.toMul.val),
    fun q => by
      apply LinearMap.ext
      intro u
      induction q using QuotientGroup.induction_on with
      | H g =>
        apply Subtype.ext
        change Units.map (algebraMap L M).toMonoidHom
            ((galoisTowerQuotientEquiv K L M (QuotientGroup.mk g)) •
              (Additive.toMul (Rep.toAdditive u) : Lˣ)) =
          g • Units.map (algebraMap L M).toMonoidHom
            (Additive.toMul (Rep.toAdditive u) : Lˣ)
        apply Units.ext
        exact AlgEquiv.restrictNormal_commutes g L _ ⟩

/-- The original middle-field unit inclusion is bijective onto the
actual restriction-kernel invariants, by genuine Galois fixed-field descent. -/
theorem galoisTowerQuotientUnitInclusion_bijective :
    Function.Bijective (galoisTowerQuotientUnitInclusion K L M).hom := by
  haveI : FiniteDimensional L M := FiniteDimensional.right K L M
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  constructor
  · intro u v huv
    change u.toMul = v.toMul
    apply Units.map_injective (algebraMap L M).injective
    exact congrArg Subtype.val huv
  · intro x
    have hx : x.val ∈ (Rep.ofAlgebraAutOnUnits L M).ρ.invariants := by
      intro g
      exact x.property ((galoisTowerKernelEquiv K L M).symm g)
    obtain ⟨u, hu⟩ := galoisUnitInvariant_exists_base (K := L) (L := M) x.val hx
    refine ⟨Additive.ofMul u, ?_⟩
    apply Subtype.ext
    exact hu

end
end Dubon2026
