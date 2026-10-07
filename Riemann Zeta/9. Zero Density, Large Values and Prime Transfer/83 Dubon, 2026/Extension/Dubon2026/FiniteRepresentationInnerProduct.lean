import Dubon2026.PrincipalCuspOrbit
import Mathlib.Analysis.InnerProductSpace.Defs

/-! # Positive invariant inner products for finite congruence representations

These are auxiliary finite-dimensional inner products obtained by group averaging.
They are not identified with the Petersson integral.
-/

namespace Dubon2026

noncomputable section

/-- Coordinates in a finite complex basis supply an actual positive-definite inner product. -/
@[reducible]
def finiteBasisInnerCore {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I]
    (b : Module.Basis I ℂ V) : InnerProductSpace.Core ℂ V where
  inner x y := ∑ i, starRingEnd ℂ (b.equivFun x i) * b.equivFun y i
  conj_inner_symm x y := by simp [map_sum, mul_comm]
  re_inner_nonneg x := by
    change 0 ≤ (∑ i, starRingEnd ℂ (b.equivFun x i) * b.equivFun x i).re
    simp only [← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re]
    exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  add_left x y z := by simp [map_add, add_mul, Finset.sum_add_distrib]
  smul_left x y c := by simp [map_mul, mul_assoc, Finset.mul_sum]
  definite x hx := by
    have hre : ∑ i, Complex.normSq (b.equivFun x i) = 0 := by
      simpa only [← Complex.normSq_eq_conj_mul_self, Complex.re_sum,
        Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re hx
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => Complex.normSq_nonneg (b.equivFun x i))).mp hre
    apply b.equivFun.injective
    ext i
    simpa using (Complex.normSq_eq_zero.mp (hall i (Finset.mem_univ i)))

/-- Averaging a positive-definite core over a finite group remains positive definite. -/
@[reducible]
def finiteRepresentationAverageCore {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (c : InnerProductSpace.Core ℂ V) : InnerProductSpace.Core ℂ V where
  inner x y := ∑ g, c.inner (ρ g x) (ρ g y)
  conj_inner_symm x y := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun g _ => c.conj_inner_symm _ _)
  re_inner_nonneg x := by
    change 0 ≤ (∑ g, c.inner (ρ g x) (ρ g x)).re
    rw [Complex.re_sum]
    exact Finset.sum_nonneg (fun g _ => c.re_inner_nonneg _)
  add_left x y z := by simp only [map_add, c.add_left, Finset.sum_add_distrib]
  smul_left x y a := by simp only [map_smul, c.smul_left, Finset.mul_sum]
  definite x hx := by
    have hre : ∑ g, (c.inner (ρ g x) (ρ g x)).re = 0 := by
      simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re hx
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun g (_ : g ∈ Finset.univ) => c.re_inner_nonneg (ρ g x))).mp hre
    have hreal : (c.inner x x).re = 0 := by simpa using hall 1 (Finset.mem_univ 1)
    apply c.definite x
    apply Complex.ext hreal
    exact Complex.conj_eq_iff_im.mp (c.conj_inner_symm x x)

/-- The averaged inner product is invariant under the actual finite-group representation. -/
theorem finiteRepresentationAverageCore_invariant {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (c : InnerProductSpace.Core ℂ V) (g : G) (x y : V) :
    (finiteRepresentationAverageCore ρ c).inner (ρ g x) (ρ g y) =
      (finiteRepresentationAverageCore ρ c).inner x y := by
  change (∑ h, c.inner (ρ h (ρ g x)) (ρ h (ρ g y))) = ∑ h, c.inner (ρ h x) (ρ h y)
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulRight g) (fun h => c.inner (ρ h x) (ρ h y))

/-- Every finite-dimensional complex representation of a finite group has a proved invariant core. -/
theorem exists_finiteRepresentation_invariantCore {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∃ c : InnerProductSpace.Core ℂ V, ∀ g x y, c.inner (ρ g x) (ρ g y) = c.inner x y :=
  ⟨finiteRepresentationAverageCore ρ (finiteBasisInnerCore (Module.finBasis ℂ V)),
    finiteRepresentationAverageCore_invariant ρ _⟩

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups
attribute [local instance] principalNormal

/-- The actual principal-level slash orbit admits a positive, invariant auxiliary inner product. -/
theorem principalCuspOrbit_invariantCore (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    ∃ c : InnerProductSpace.Core ℂ (principalCuspOrbit N k f),
      ∀ g x y, c.inner (principalCuspOrbitRepresentation N k f g x)
        (principalCuspOrbitRepresentation N k f g y) = c.inner x y := by
  letI := Fintype.ofFinite (SL(2, ℤ) ⧸ Gamma N)
  exact exists_finiteRepresentation_invariantCore (principalCuspOrbitRepresentation N k f)

end
end Dubon2026
