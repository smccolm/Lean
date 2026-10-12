import Dubon2026.LocalFieldFiniteCyclicNormPeriod

/-! # The period-normalized norm-residue map for the original cyclic extension -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(E/K)]
  (g : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

attribute [local instance] IsCyclic.commGroup

/-- The actual cyclic norm quotient is identified with the original
Galois group using the original cocycle period and normalized invariant.
Independence of the displayed generator is a separate obligation. -/
def localFieldFiniteCyclicNormResidueEquiv :
    (Additive Kˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := E))) ≃+
      Additive Gal(E/K) :=
  ((localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg).symm.toAddEquiv.trans
    (localFieldFiniteStageH2CyclicEquiv K Ω E).toAddEquiv).trans
      (zmodAddEquivOfGenerator (G := Additive Gal(E/K)) hg (IsGalois.card_aut_eq_finrank K E))

/-- The original base-unit norm-residue homomorphism into the original
cyclic Galois group. It uses the actual quotient by field norms. -/
def localFieldFiniteCyclicNormResidue : Additive Kˣ →+ Additive Gal(E/K) :=
  (localFieldFiniteCyclicNormResidueEquiv K Ω E g hg).toAddMonoidHom.comp
    (LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := E))).mkQ.toAddMonoidHom

/-- Every original automorphism is attained by an actual base-field unit. -/
theorem localFieldFiniteCyclicNormResidue_surjective :
    Function.Surjective (localFieldFiniteCyclicNormResidue K Ω E g hg) := by
  exact (localFieldFiniteCyclicNormResidueEquiv K Ω E g hg).surjective.comp
    (Submodule.mkQ_surjective _)

/-- The kernel consists exactly of norms of actual extension-field units. -/
theorem localFieldFiniteCyclicNormResidue_eq_zero_iff (u : Additive Kˣ) :
    localFieldFiniteCyclicNormResidue K Ω E g hg u = 0 ↔
      ∃ v : Eˣ, Units.map (Algebra.norm K (S := E)) v = u.toMul := by
  change localFieldFiniteCyclicNormResidueEquiv K Ω E g hg (Submodule.Quotient.mk u) = 0 ↔ _
  rw [← (localFieldFiniteCyclicNormResidueEquiv K Ω E g hg).map_zero,
    (localFieldFiniteCyclicNormResidueEquiv K Ω E g hg).injective.eq_iff,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v.toMul, congrArg Additive.toMul hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨Additive.ofMul v, congrArg Additive.ofMul hv⟩

/-- The genuine period of the original fundamental class maps to the
displayed generator. This fixes the arithmetic orientation of the map. -/
theorem localFieldFiniteCyclicNormResidue_fundamental_period :
    localFieldFiniteCyclicNormResidueEquiv K Ω E g hg
      (localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg
        (localFieldFiniteStageFundamentalClass K Ω E)) = Additive.ofMul g := by
  change zmodAddEquivOfGenerator (G := Additive Gal(E/K)) hg
    (IsGalois.card_aut_eq_finrank K E)
      (localFieldFiniteStageH2CyclicEquiv K Ω E
        ((localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg).symm
          (localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg
            (localFieldFiniteStageFundamentalClass K Ω E)))) = _
  rw [LinearEquiv.symm_apply_apply]
  simp only [localFieldFiniteStageFundamentalClass, LinearEquiv.apply_symm_apply]
  exact zmodAddEquivOfGenerator_apply_one hg _

end
end Dubon2026
