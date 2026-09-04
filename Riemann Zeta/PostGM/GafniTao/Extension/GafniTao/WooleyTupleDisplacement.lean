import GafniTao.WooleyWeightedTuple

/-!
# Tuple displacements for polynomial Fourier systems

The finite Fourier averages in Wooley's argument retain precisely those
ordered tuple pairs whose polynomial displacement vanishes.  This file
defines that displacement for an arbitrary finite point set and proves the
exact character identity used by orthogonality.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

/-- Degree-by-degree displacement of two ordered tuples. -/
def wooleyTupleDisplacement {I : Type*}
    (q k s : ℕ) (value : I → Fin k → ZMod q)
    (xy : WooleyFiniteTuple s I × WooleyFiniteTuple s I) :
    Fin k → ZMod q := fun j =>
  (∑ i, value (xy.1 i) j) - ∑ i, value (xy.2 i) j

/-- The coordinate-product additive character of one point. -/
def wooleyPointCharacter {I : Type*}
    (q k : ℕ) [NeZero q] (value : I → Fin k → ZMod q)
    (alpha : Fin k → ZMod q) (x : I) : ℂ :=
  ∏ j, ZMod.stdAddChar (alpha j * value x j)

theorem wooley_tuple_point_character
    {I : Type*} (q k s : ℕ) [NeZero q]
    (value : I → Fin k → ZMod q)
    (alpha : Fin k → ZMod q) (x : WooleyFiniteTuple s I) :
    ∏ i, wooleyPointCharacter q k value alpha (x i) =
      ∏ j, ZMod.stdAddChar
        (alpha j * ∑ i, value (x i) j) := by
  unfold wooleyPointCharacter
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← wooley_addChar_sum_eq_prod]
  congr 1
  rw [Finset.mul_sum]

/-- Product of the positive and conjugated negative tuple phases is the
character of their displacement. -/
theorem wooley_tuple_pair_character
    {I : Type*} (q k s : ℕ) [NeZero q]
    (value : I → Fin k → ZMod q)
    (alpha : Fin k → ZMod q)
    (xy : WooleyFiniteTuple s I × WooleyFiniteTuple s I) :
    wooleyTuplePhase s (wooleyPointCharacter q k value alpha) xy =
      ∏ j, ZMod.stdAddChar
        (alpha j * wooleyTupleDisplacement q k s value xy j) := by
  unfold wooleyTuplePhase
  rw [wooley_tuple_point_character, wooley_tuple_point_character]
  rw [map_prod]
  simp_rw [← AddChar.map_neg_eq_conj]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [wooleyTupleDisplacement]
  ring

/-- Evaluation vector of an integer polynomial system modulo `q`. -/
def wooleyPolynomialValue {k : ℕ} (phi : WooleyPolynomialSystem k)
    (q : ℕ) (n : ℤ) : Fin k → ZMod q := fun j =>
  (((phi j).eval n : ℤ) : ZMod q)

theorem wooleySourcePolynomialPhase_eq_pointCharacter
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (alpha : Fin k → ZMod q) (n : ℤ) :
    wooleySourcePolynomialPhase phi alpha n =
      wooleyPointCharacter q k (wooleyPolynomialValue phi q) alpha n := by
  unfold wooleySourcePolynomialPhase wooleyPointCharacter
    wooleyPolynomialValue
  exact wooley_addChar_sum_eq_prod ZMod.stdAddChar _

/-- The source polynomial tuple phase is exactly the character of the
polynomial displacement. -/
theorem wooley_source_polynomial_tuple_pair_character
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (s : ℕ) (alpha : Fin k → ZMod q)
    (xy : WooleyFiniteTuple s ℤ × WooleyFiniteTuple s ℤ) :
    wooleyTuplePhase s (wooleySourcePolynomialPhase phi alpha) xy =
      ∏ j, ZMod.stdAddChar
        (alpha j * wooleyTupleDisplacement q k s
          (wooleyPolynomialValue phi q) xy j) := by
  unfold wooleyTuplePhase
  simp_rw [wooleySourcePolynomialPhase_eq_pointCharacter]
  change wooleyTuplePhase s
      (wooleyPointCharacter q k (wooleyPolynomialValue phi q) alpha) xy = _
  exact wooley_tuple_pair_character q k s
    (wooleyPolynomialValue phi q) alpha xy

#print axioms wooley_tuple_point_character
#print axioms wooley_tuple_pair_character
#print axioms wooleySourcePolynomialPhase_eq_pointCharacter
#print axioms wooley_source_polynomial_tuple_pair_character

end

end GafniTao
