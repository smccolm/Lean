import Dubon2026.ContinuousCyclicGaloisUnitH2Classes

/-! # Actual base units and original generator-invariant Galois coefficients -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

attribute [local instance] IsCyclic.commGroup

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- The actual base-unit inclusion identifies original units with the
original generator-invariant coefficient module, by genuine Galois descent. -/
def galoisGeneratorInvariantBaseEquiv : Additive Kˣ ≃ₗ[ℤ]
    LinearMap.ker (Rep.applyAsHom (Rep.ofAlgebraAutOnUnits K L) g -
      𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap := by
  apply LinearEquiv.ofBijective (galoisUnitsBaseInvariant g)
  constructor
  · intro u v huv
    apply Additive.toMul.injective
    apply galoisUnitsBaseCoefficient_injective (L := L)
    exact congrArg Subtype.val huv
  · intro v
    have hv : v.val ∈ (Rep.ofAlgebraAutOnUnits K L).ρ.invariants := by
      apply (Representation.mem_invariants_iff_of_forall_mem_zpowers
        (Rep.ofAlgebraAutOnUnits K L).ρ g hg v.val).mpr
      have he := v.property
      change (Rep.ofAlgebraAutOnUnits K L).ρ g v.val - v.val = 0 at he
      exact sub_eq_zero.mp he
    obtain ⟨u, hu⟩ := galoisUnitInvariant_exists_base v.val hv
    exact ⟨Additive.ofMul u, Subtype.ext hu⟩

/-- The inverse retains the literal original coefficient, rather than an
unrelated copy of the invariant unit. -/
theorem galoisGeneratorInvariantBaseEquiv_symm_coefficient
    (x : LinearMap.ker (Rep.applyAsHom (Rep.ofAlgebraAutOnUnits K L) g -
      𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    galoisUnitsBaseCoefficient (L := L)
      ((galoisGeneratorInvariantBaseEquiv g hg).symm x).toMul = x.val := by
  exact congrArg Subtype.val ((galoisGeneratorInvariantBaseEquiv g hg).apply_symm_apply x)

end
end Dubon2026
