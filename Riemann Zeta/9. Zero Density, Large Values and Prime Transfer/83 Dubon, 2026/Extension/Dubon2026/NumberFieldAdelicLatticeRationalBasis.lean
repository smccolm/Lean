import Dubon2026.NumberFieldAdelicLatticeRank
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! # Original rational coordinates from an attached integral lattice basis

The proved full rank and rational span make each integral lattice basis
a basis of the original rational vector space. Its coordinates on the
lattice are precisely the original integer coordinates. These are the
coordinates used in DUB-17's trace-dual determinant bound.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Module

variable (K : Type*) [Field K] [NumberField K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

/-- Each integral basis of the actual attached lattice gives a basis of the original rational vector space. -/
def numberFieldAdelicLatticeRationalBasis
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g)) : Basis κ ℚ (ι → K) := by
  let L := numberFieldAdelicLattice K ι g
  let f := L.subtype.restrictScalars ℤ
  apply basisOfTopLeSpanOfCardEqFinrank (f ∘ b)
  · rw [← Submodule.span_span_of_tower ℤ, Set.range_comp, ← Submodule.map_span,
      b.span_eq, Submodule.map_top]
    have hf : (f.range : Set (ι → K)) = L := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hf]
    rw [numberFieldAdelicLattice_span_rat]
  · rw [← finrank_eq_card_basis b, numberFieldAdelicLattice_finrank,
      Module.finrank_pi_fintype]
    simp

/-- The rational basis retains exactly the original lattice vectors. -/
theorem numberFieldAdelicLatticeRationalBasis_apply
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g)) (i : κ) :
    numberFieldAdelicLatticeRationalBasis K ι g b i = (b i).val := by
  simp only [numberFieldAdelicLatticeRationalBasis,
    coe_basisOfTopLeSpanOfCardEqFinrank, Function.comp_apply,
    LinearMap.restrictScalars_apply, Submodule.subtype_apply]

/-- Original lattice coordinates are unchanged except for their canonical rational cast. -/
theorem numberFieldAdelicLatticeRationalBasis_repr
    (g : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g))
    (x : numberFieldAdelicLattice K ι g) (i : κ) :
    (numberFieldAdelicLatticeRationalBasis K ι g b).repr x.val i = (b.repr x i : ℚ) := by
  let B := numberFieldAdelicLatticeRationalBasis K ι g b
  have he : B.repr.toLinearMap.restrictScalars ℤ ∘ₗ
      (numberFieldAdelicLattice K ι g).subtype.restrictScalars ℤ =
        Finsupp.mapRange.linearMap (Algebra.linearMap ℤ ℚ) ∘ₗ b.repr.toLinearMap := by
    apply b.ext
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, Submodule.subtype_apply, B,
      ← numberFieldAdelicLatticeRationalBasis_apply K ι g b, Basis.repr_self,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]
  exact DFunLike.congr_fun (LinearMap.congr_fun he x) i

end
end Dubon2026
