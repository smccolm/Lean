import GafniTao.WooleyOrthogonalityInsertion
import GafniTao.WooleySourceMean

/-!
# Weighted tuple expansions for finite Fourier means

This file supplies the exact algebra behind expanding a `2s`-th moment into
two ordered `s`-tuples.  It keeps coefficients and phases arbitrary, so the
same theorem applies to Wooley's original residue sum, the translated
`c_y(alpha)` sum, and their product in (7.17).
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

abbrev WooleyFiniteTuple (s : ℕ) (I : Type*) := Fin s → I

/-- The coefficient attached to a pair of ordered tuples after expanding an
absolute `2s`-th power. -/
def wooleyTupleCoefficient {I : Type*}
    (s : ℕ) (coefficient : I → ℂ)
    (xy : WooleyFiniteTuple s I × WooleyFiniteTuple s I) : ℂ :=
  (∏ i, coefficient (xy.1 i)) * conj (∏ i, coefficient (xy.2 i))

/-- The corresponding phase attached to a pair of tuples. -/
def wooleyTuplePhase {I : Type*}
    (s : ℕ) (phase : I → ℂ)
    (xy : WooleyFiniteTuple s I × WooleyFiniteTuple s I) : ℂ :=
  (∏ i, phase (xy.1 i)) * conj (∏ i, phase (xy.2 i))

/-- Exact ordered-tuple expansion of a weighted absolute moment. -/
theorem wooley_weighted_sum_abs_pow_expand
    {I : Type*} [Fintype I] (s : ℕ)
    (coefficient phase : I → ℂ) :
    (∑ n : I, coefficient n * phase n) ^ s *
        conj (∑ n : I, coefficient n * phase n) ^ s =
      ∑ xy : WooleyFiniteTuple s I × WooleyFiniteTuple s I,
        wooleyTupleCoefficient s coefficient xy *
          wooleyTuplePhase s phase xy := by
  rw [Fintype.sum_pow]
  rw [← map_pow, Fintype.sum_pow, map_sum]
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [wooleyTupleCoefficient, wooleyTuplePhase]
  rw [Finset.prod_mul_distrib]
  simp only [map_prod, map_mul]
  rw [Finset.prod_mul_distrib]
  ring

/-- A source Finsupp sum can be read as a sum over its support subtype. -/
theorem wooleySource_sum_eq_support_subtype
    (gamma : WooleySourceSequence) (f : ℤ → ℂ) :
    ∑ n ∈ gamma.support, gamma n * f n =
      ∑ n : ↑gamma.support, gamma n * f n := by
  exact (Finset.sum_attach gamma.support
    (fun n => gamma n * f n)).symm

#print axioms wooley_weighted_sum_abs_pow_expand
#print axioms wooleySource_sum_eq_support_subtype

end

end GafniTao
