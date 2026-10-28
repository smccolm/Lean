import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import P2M.Util
namespace P2MW.S_AlgebraicCurve_isIntegral_adjoin_map_algHom

set_option autoImplicit false

theorem solution {K F F' : Type*} [CommRing K] [CommRing F] [CommRing F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') {j x : F} (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin K {φ j}) (φ x) := by
  have hle : (Algebra.adjoin K {j}).map φ ≤ Algebra.adjoin K {φ j} := by
    rw [Subalgebra.map_le]
    refine Algebra.adjoin_le fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    show j ∈ Subalgebra.comap φ (Algebra.adjoin K {φ j})
    rw [Subalgebra.mem_comap]
    exact Algebra.subset_adjoin rfl
  have hmem : ∀ a : ↥(Algebra.adjoin K {j}),
      (φ.comp (Algebra.adjoin K {j}).val) a ∈ Algebra.adjoin K {φ j} :=
    fun a => hle (Subalgebra.mem_map.mpr ⟨(a : F), a.2, rfl⟩)
  have key := IsIntegral.map_of_comp_eq
    ((φ.comp (Algebra.adjoin K {j}).val).codRestrict (Algebra.adjoin K {φ j}) hmem).toRingHom
    φ.toRingHom (by ext a; rfl) hx
  exact key
