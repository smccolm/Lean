import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Adjoin.Basic

/-! DUB-17/18 -> rational Fourier spanning -> holomorphic recovery of integral
Fricke Laurent summands. Extract the finite monic relation over the original
constant-coordinate algebra. This is the range-indexed form needed by the
existing monic-root bound and the holomorphic quotient consumer.
The existing same-coefficient Laurent extraction was reviewed; here the
constant field and ambient field differ, and no coefficient-field ascent
or descent assumption is inserted. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem exists_coordinate_monic_relation {R A : Type*} [Field R] [Field A] [Algebra R A]
    {J X : A} (hX : IsIntegral (Algebra.adjoin R ({J} : Set A)) X) :
    ∃ (d : ℕ) (p : ℕ → Polynomial R),
      X ^ d + ∑ i ∈ Finset.range d, Polynomial.aeval J (p i) * X ^ i = 0 := by
  classical
  obtain ⟨Q, hQ, he⟩ := hX
  have hcoeff (n : ℕ) : ∃ P : Polynomial R,
      Polynomial.aeval J P = ((Q.coeff n : _) : A) :=
    (Algebra.adjoin_singleton_eq_range_aeval R J).le (Q.coeff n).property
  choose p hp using hcoeff
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hQ.coeff_natDegree,
    map_one, one_mul] at he
  change (∑ n ∈ Finset.range Q.natDegree,
    ((Q.coeff n : _) : A) * X ^ n) + X ^ Q.natDegree = 0 at he
  simp only [← hp] at he
  exact ⟨Q.natDegree, p, by simpa only [add_comm] using he⟩

end
end Dubon2026.SourceFunctionField
