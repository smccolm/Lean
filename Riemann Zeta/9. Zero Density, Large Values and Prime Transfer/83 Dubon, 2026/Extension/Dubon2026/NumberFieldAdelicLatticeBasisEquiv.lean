import Dubon2026.NumberFieldAdelicLatticeRationalBasis

/-! # Extending the actual integral lattice basis equivalence to the rationals

The original rational bases give an equivalence of the original vector
space whose restriction is precisely the integral basis equivalence.
It sends the actual attached lattice onto its counterpart. This serves
DUB-17's recovery of a source unitary double coset from equal invariants.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Module

variable (K : Type*) [Field K] [NumberField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The rational equivalence determined by the two original attached lattice bases. -/
def numberFieldAdelicLatticeRationalEquiv
    (g h : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h)) : (ι → K) ≃ₗ[ℚ] (ι → K) :=
  (numberFieldAdelicLatticeRationalBasis K ι g b).equiv
    (numberFieldAdelicLatticeRationalBasis K ι h c) (Equiv.refl κ)

/-- The rational equivalence sends each original integral basis vector to its counterpart. -/
theorem numberFieldAdelicLatticeRationalEquiv_basis
    (g h : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h)) (i : κ) :
    numberFieldAdelicLatticeRationalEquiv K g h b c (b i).val = (c i).val := by
  rw [← numberFieldAdelicLatticeRationalBasis_apply K ι g b i]
  exact (Basis.equiv_apply _ _ _ _).trans
    (numberFieldAdelicLatticeRationalBasis_apply K ι h c i)

/-- The original rational equivalence restricts to precisely the original integral basis equivalence. -/
theorem numberFieldAdelicLatticeRationalEquiv_integral
    (g h : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h))
    (x : numberFieldAdelicLattice K ι g) :
    numberFieldAdelicLatticeRationalEquiv K g h b c x.val =
      (b.equiv c (Equiv.refl κ) x).val := by
  have he : (numberFieldAdelicLatticeRationalEquiv K g h b c).toLinearMap.restrictScalars ℤ ∘ₗ
      (numberFieldAdelicLattice K ι g).subtype.restrictScalars ℤ =
      (numberFieldAdelicLattice K ι h).subtype.restrictScalars ℤ ∘ₗ
        (b.equiv c (Equiv.refl κ)).toLinearMap := by
    apply b.ext
    intro i
    simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, Submodule.subtype_apply, Basis.equiv_apply, Equiv.refl_apply] using
        numberFieldAdelicLatticeRationalEquiv_basis K g h b c i
  exact LinearMap.congr_fun he x

/-- The original rational basis equivalence sends the original attached lattice onto its counterpart. -/
theorem numberFieldAdelicLatticeRationalEquiv_image
    (g h : Matrix.GeneralLinearGroup ι (FiniteAdeleRing (𝓞 K) K))
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h)) :
    numberFieldAdelicLatticeRationalEquiv K g h b c ''
      (numberFieldAdelicLattice K ι g : Set (ι → K)) = numberFieldAdelicLattice K ι h := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have he := numberFieldAdelicLatticeRationalEquiv_integral K g h b c ⟨x, hx⟩
    rw [he]
    exact (b.equiv c (Equiv.refl κ) ⟨x, hx⟩).property
  · intro y hy
    obtain ⟨x, hx⟩ := (b.equiv c (Equiv.refl κ)).surjective ⟨y, hy⟩
    refine ⟨x.val, x.property, ?_⟩
    rw [numberFieldAdelicLatticeRationalEquiv_integral, hx]

end
end Dubon2026
