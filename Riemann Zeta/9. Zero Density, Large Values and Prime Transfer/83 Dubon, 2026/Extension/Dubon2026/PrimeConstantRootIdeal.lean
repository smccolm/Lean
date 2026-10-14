import Dubon2026.MonicResidueIrreducibleDVR
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! # The actual root ideal for a prime constant coefficient

For the required cyclotomic and changed primitive polynomials, the constant
coefficient is a uniformizer of the original DVR. The quotient by the
actual adjoined root is its residue field, so that root ideal is maximal.
Together with Eisenstein this will identify the genuine valuation rings
and uniformizers needed by DUB-17's unramified-compositum argument.
-/
namespace Dubon2026
noncomputable section
open Polynomial IsLocalRing

/-- Reduction modulo the actual root evaluates every original polynomial at zero. -/
theorem adjoinRoot_quotient_root_eval {R : Type*} [CommRing R] (f g : R[X]) :
    let J : Ideal (AdjoinRoot f) := Ideal.span {AdjoinRoot.root f}
    Ideal.Quotient.mk J (AdjoinRoot.mk f g) =
      Ideal.Quotient.mk J (algebraMap R (AdjoinRoot f) (g.coeff 0)) := by
  dsimp only
  rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def, Polynomial.hom_eval₂]
  have hz : Ideal.Quotient.mk (Ideal.span {AdjoinRoot.root f}) (AdjoinRoot.root f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hz, Polynomial.eval₂_at_zero, RingHom.comp_apply]

/-- A prime constant coefficient makes the actual root ideal maximal over the original DVR. -/
theorem prime_constant_adjoinRoot_root_maximal {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (f : R[X]) (π : R) (hπ : Prime π) (h0 : f.coeff 0 = π) :
    (Ideal.span {AdjoinRoot.root f} : Ideal (AdjoinRoot f)).IsMaximal := by
  let J : Ideal (AdjoinRoot f) := Ideal.span {AdjoinRoot.root f}
  have hmax : maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ.irreducible
  have hπ0 : residue R π = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hmax]
    exact Ideal.subset_span (Set.mem_singleton _)
  let φ : AdjoinRoot f →+* ResidueField R := AdjoinRoot.lift (f := f) (residue R) 0 (by
    rw [Polynomial.eval₂_at_zero, h0, hπ0])
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨r, hr⟩ := residue_surjective y
    refine ⟨algebraMap R (AdjoinRoot f) r, ?_⟩
    change AdjoinRoot.lift (f := f) (residue R) 0 _ (AdjoinRoot.of f r) = y
    rw [AdjoinRoot.lift_of, hr]
  have hker : RingHom.ker φ = J := by
    apply le_antisymm
    · intro x hx
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
      have hg : residue R (g.coeff 0) = 0 := by
        change AdjoinRoot.lift (f := f) (residue R) 0 _ (AdjoinRoot.mk f g) = 0 at hx
        rwa [AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero] at hx
      have hd : π ∣ g.coeff 0 := by
        apply Ideal.mem_span_singleton.mp
        rw [← hmax]
        exact Ideal.Quotient.eq_zero_iff_mem.mp hg
      obtain ⟨r, hr⟩ := hd
      have hπJ : Ideal.Quotient.mk J (algebraMap R (AdjoinRoot f) π) = 0 := by
        have h := adjoinRoot_quotient_root_eval f f
        dsimp only at h
        rw [AdjoinRoot.mk_self, map_zero, h0] at h
        exact h.symm
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [adjoinRoot_quotient_root_eval, hr, map_mul, map_mul, hπJ, zero_mul]
    · apply Ideal.span_le.mpr
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      change AdjoinRoot.lift (f := f) (residue R) 0 _ (AdjoinRoot.root f) = 0
      exact AdjoinRoot.lift_root _
  change J.IsMaximal
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective φ hsurj

end
end Dubon2026
