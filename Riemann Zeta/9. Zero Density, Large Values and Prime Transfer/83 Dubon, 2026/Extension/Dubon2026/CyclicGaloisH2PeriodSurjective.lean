import Dubon2026.GaloisUnitCarryCocycle
import Dubon2026.CyclicGaloisH2PeriodNormMap

/-! # Explicit original cocycles realize every original cyclic norm-quotient class -/

namespace Dubon2026
noncomputable section

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Actual carry cocycles realize every norm-quotient class. The degree-one
case is discharged by the actual field norm of the original scalar unit. -/
theorem cyclicGaloisH2PeriodNormMap_surjective :
    Function.Surjective (cyclicGaloisH2PeriodNormMap g hg) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
    by_cases hn : 1 < Nat.card Gal(L/K)
    · refine ⟨Submodule.Quotient.mk (galoisUnitCarryCocycle g hg u.toMul), ?_⟩
      rw [cyclicGaloisH2PeriodNormMap_mk, galoisUnitCarryCocycle_period g hg _ hn]
      rfl
    · have hn' : Nat.card Gal(L/K) = 1 := by
        have hpos : 0 < Nat.card Gal(L/K) := Nat.card_pos
        omega
      have hu : u ∈ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L)) := by
        refine ⟨Additive.ofMul (Units.map (algebraMap K L).toMonoidHom u.toMul), ?_⟩
        apply Additive.toMul.injective
        apply Units.ext
        change Algebra.norm K (algebraMap K L u.toMul.val) = u.toMul.val
        rw [Algebra.norm_algebraMap, ← IsGalois.card_aut_eq_finrank, hn', pow_one]
      exact ⟨0, by rw [map_zero]; exact ((Submodule.Quotient.mk_eq_zero _).mpr hu).symm⟩

/-- When the original norm quotient is finite, the explicit original
period map is bijective. The previous cyclic cohomology computation supplies
only the equality of finite cardinalities; no map comparison is asserted. -/
theorem cyclicGaloisH2PeriodNormMap_bijective
    [Finite (Additive Kˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L)))] :
    Function.Bijective (cyclicGaloisH2PeriodNormMap g hg) := by
  haveI : Finite (GaloisUnitContinuousH2 (K := K) (Ω := L)) :=
    Finite.of_equiv _ (continuousCyclicGaloisNormQuotientEquiv g hg).toEquiv
  have hsurj := cyclicGaloisH2PeriodNormMap_surjective g hg
  exact ⟨(Finite.injective_iff_surjective_of_equiv
    (continuousCyclicGaloisNormQuotientEquiv g hg).symm.toEquiv).mpr hsurj, hsurj⟩

end
end Dubon2026
