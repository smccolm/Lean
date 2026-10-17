import Dubon2026.LocalFieldFiniteCyclicReciprocity
import Mathlib.RingTheory.Norm.Transitivity

/-! # Upper-field norms vanish under cyclic-subfield reciprocity

The literal norm tower transports a norm from the full cyclotomic field
to its cyclic subfield. This is the prime-two cancellation needed by the
ramified principal product on DUB-17's invariant-sum and class-generator route.
-/
namespace Dubon2026
noncomputable section

/-- An actual norm from a containing field has trivial original local
reciprocity on the cyclic subfield. -/
theorem localFieldFiniteCyclicReciprocity_eq_one_of_overfield_norm
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (L F : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(L/K)]
    (hLF : L.toIntermediateField ≤ F.toIntermediateField) (x : Kˣ)
    (hx : ∃ v : Fˣ, Units.map (Algebra.norm K (S := F)) v = x) :
    (localFieldFiniteCyclicReciprocity K Ω L (Additive.ofMul x)).toMul = 1 := by
  let i : L →ₐ[K] F := IntermediateField.inclusion hLF
  letI : Algebra L F := i.toAlgebra
  letI : IsScalarTower K L F := IsScalarTower.of_algHom i
  letI : FiniteDimensional L F := FiniteDimensional.right K L F
  obtain ⟨v, hv⟩ := hx
  have hzero : localFieldFiniteCyclicReciprocity K Ω L (Additive.ofMul x) = 0 := by
    apply (localFieldFiniteCyclicReciprocity_eq_zero_iff K Ω L (Additive.ofMul x)).mpr
    refine ⟨Units.map (Algebra.norm L (S := F)) v, ?_⟩
    apply Units.ext
    change Algebra.norm K (Algebra.norm L (v : F)) = (x : K)
    rw [Algebra.norm_norm]
    exact congrArg Units.val hv
  exact congrArg Additive.toMul hzero

end
end Dubon2026
