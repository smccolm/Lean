import Dubon2026.ContinuousCyclicGaloisUnitH2Classes
import Mathlib.LinearAlgebra.Isomorphisms

/-! # The actual cyclic Galois unit norm quotient is original continuous H2 -/

namespace Dubon2026
noncomputable section

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- The original extension-field unit norm, as its genuine integer-linear
map on the actual additive tags of the original unit groups. -/
def galoisUnitFieldNormLinear : Additive Lˣ →ₗ[ℤ] Additive Kˣ :=
  (Units.map (Algebra.norm K (S := L))).toAdditive.toIntLinearMap

/-- The kernel of the actual cyclic class map is exactly the range of the
original field-unit norm, with no replacement by an abstract norm certificate. -/
theorem continuousCyclicGaloisUnitH2Class_ker :
    LinearMap.ker (continuousCyclicGaloisUnitH2Class g hg) =
      LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L)) := by
  ext u
  change continuousCyclicGaloisUnitH2Class g hg u = 0 ↔ _
  rw [continuousCyclicGaloisUnitH2Class_eq_zero_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨Additive.ofMul v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v.toMul, hv⟩

/-- The actual base-field units modulo original extension-field norms are
linearly equivalent to the existing continuous H2 of the original cyclic
Galois action. The generator is explicit and not identified with Frobenius. -/
def continuousCyclicGaloisNormQuotientEquiv :
    (Additive Kˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L))) ≃ₗ[ℤ]
      GaloisUnitContinuousH2 (K := K) (Ω := L) :=
  (Submodule.quotEquivOfEq _ _ (continuousCyclicGaloisUnitH2Class_ker g hg).symm).trans
    ((continuousCyclicGaloisUnitH2Class g hg).quotKerEquivOfSurjective
      (continuousCyclicGaloisUnitH2Class_surjective g hg))

/-- The actual norm-quotient equivalence sends each original base unit to
its original continuous cyclic cohomology class. -/
theorem continuousCyclicGaloisNormQuotientEquiv_mk (u : Additive Kˣ) :
    continuousCyclicGaloisNormQuotientEquiv g hg (Submodule.Quotient.mk u) =
      continuousCyclicGaloisUnitH2Class g hg u := by
  rfl

end
end Dubon2026
