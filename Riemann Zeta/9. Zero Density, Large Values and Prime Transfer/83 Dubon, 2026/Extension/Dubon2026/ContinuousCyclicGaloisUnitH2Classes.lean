import Dubon2026.GaloisUnitInvariantBaseDescent
import Dubon2026.ContinuousKummerH2Maps
import Dubon2026.ContinuousFiniteCyclicH2

/-! # Original continuous cyclic Galois unit H2 classes from actual base units -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

attribute [local instance] IsCyclic.commGroup

variable (g : Gal(L/K))

/-- The actual base-unit inclusion lands in the original generator-invariant
coefficient submodule, by the actual Galois action on the base field. -/
def galoisUnitsBaseInvariant : Additive Kˣ →ₗ[ℤ]
    LinearMap.ker (Rep.applyAsHom (Rep.ofAlgebraAutOnUnits K L) g -
      𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap := by
  let φ : Additive Kˣ →ₗ[ℤ] Rep.ofAlgebraAutOnUnits K L :=
    (Units.map (algebraMap K L).toMonoidHom).toAdditive.toIntLinearMap
  refine φ.codRestrict _ (fun u => ?_)
  change (Rep.ofAlgebraAutOnUnits K L).ρ g (galoisUnitsBaseCoefficient u.toMul) -
    galoisUnitsBaseCoefficient u.toMul = 0
  rw [galoisUnitsBaseCoefficient_fixed, sub_self]

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- The original cyclic cohomology class of a genuine base-field unit, using
the pinned cyclic computation and original continuous/algebraic comparison. -/
def continuousCyclicGaloisUnitH2Class : Additive Kˣ →ₗ[ℤ]
    GaloisUnitContinuousH2 (K := K) (Ω := L) :=
  (continuousFiniteCyclicH2Pi (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) g hg).comp
      (galoisUnitsBaseInvariant g)

/-- The original class of a base-field unit vanishes exactly when that same
unit is the actual norm of an original extension-field unit. -/
theorem continuousCyclicGaloisUnitH2Class_eq_zero_iff (u : Additive Kˣ) :
    continuousCyclicGaloisUnitH2Class g hg u = 0 ↔
      ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u.toMul := by
  change continuousFiniteCyclicH2Pi (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) g hg
      (galoisUnitsBaseInvariant g u) = 0 ↔ _
  rw [continuousFiniteCyclicH2Pi_eq_zero_iff]
  exact galoisUnitsBaseCoefficient_mem_normRange_iff u.toMul

/-- Every original continuous cyclic Galois unit H2 class is represented by
an actual base-field unit, using actual invariant descent rather than an
assumed identification of the invariant coefficient module. -/
theorem continuousCyclicGaloisUnitH2Class_surjective :
    Function.Surjective (continuousCyclicGaloisUnitH2Class g hg) := by
  intro x
  obtain ⟨v, rfl⟩ := continuousFiniteCyclicH2Pi_surjective (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) g hg x
  have hv : v.val ∈ (Rep.ofAlgebraAutOnUnits K L).ρ.invariants := by
    apply (Representation.mem_invariants_iff_of_forall_mem_zpowers
      (Rep.ofAlgebraAutOnUnits K L).ρ g hg v.val).mpr
    have he := v.property
    change (Rep.ofAlgebraAutOnUnits K L).ρ g v.val - v.val = 0 at he
    exact sub_eq_zero.mp he
  obtain ⟨u, hu⟩ := galoisUnitInvariant_exists_base v.val hv
  refine ⟨Additive.ofMul u, ?_⟩
  change continuousFiniteCyclicH2Pi (Rep.ofAlgebraAutOnUnits K L)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) g hg
        (galoisUnitsBaseInvariant g (Additive.ofMul u)) = _
  congr 1
  exact Subtype.ext hu

/-- Equality of original cyclic H2 classes means precisely that the ratio
of their actual base-field units is an actual extension-field norm. -/
theorem continuousCyclicGaloisUnitH2Class_eq_iff (u v : Kˣ) :
    continuousCyclicGaloisUnitH2Class g hg (Additive.ofMul u) =
        continuousCyclicGaloisUnitH2Class g hg (Additive.ofMul v) ↔
      ∃ w : Lˣ, Units.map (Algebra.norm K (S := L)) w = u / v := by
  rw [← sub_eq_zero, ← map_sub, continuousCyclicGaloisUnitH2Class_eq_zero_iff]
  rfl

end
end Dubon2026
