import RiemannZeta.GuthMaynard.ClassicalEndpointSlab

/-!
# The coefficient-one zeta pattern in the Heath--Brown high cell

This file gives names to the literal coefficient-one Dirichlet sums occurring
inside the frozen Type-I Fourier-deweighting identities.  These are finite
objects, not an assumed large-values estimate.  The interval conventions are
kept in the definitions so that later use of Heath--Brown's twelfth-moment
argument cannot silently change an endpoint.
-/

open Complex Finset MeasureTheory Real
open scoped BigOperators FourierTransform SchwartzMap

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The negative-sign coefficient-one Dirichlet sum on the half-open integer
interval `(L,U]`.  This is the finite zeta pattern used by the Type-I
Fourier-deweighting step. -/
noncomputable def heathBrownZetaIntervalSum
    (L U : Nat) (t : Real) : Complex :=
  ∑ n ∈ Finset.Ioc L U,
    (n : Complex) ^ (-(t : Complex) * Complex.I)

/-- The exact prefix convention appearing in
`typeISourceSmoothBlock_fourierDeweight`: the integers in `[1,A+1]`. -/
noncomputable def heathBrownZetaPrefixSum
    (A : Nat) (t : Real) : Complex :=
  ∑ n ∈ Finset.Icc 1 (A + 1),
    (n : Complex) ^ (-(t : Complex) * Complex.I)

/-- The named half-open interval sum is exactly the frozen dyadic polynomial
with literal coefficient one. -/
theorem heathBrownZetaIntervalSum_dyadic
    (N : Nat) (t : Real) :
    heathBrownZetaIntervalSum N (2 * N) t =
      dirichletPoly N (fun _ => (1 : Complex)) t := by
  simp [heathBrownZetaIntervalSum, dirichletPoly, dyadicInterval]

/-- Reversing the ordinate converts the same literal coefficient-one sum to
the positive-sign source convention, with no coefficient twist. -/
theorem heathBrownZetaIntervalSum_dyadic_neg
    (N : Nat) (t : Real) :
    heathBrownZetaIntervalSum N (2 * N) (-t) =
      sourceDirichletPoly N (fun _ => (1 : Complex)) t := by
  rw [heathBrownZetaIntervalSum_dyadic]
  unfold dirichletPoly sourceDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  push_cast
  ring

/-- `[1,A+1]` and `(0,A+1]` are literally the same natural-number interval.
This records the endpoint bridge used when prefixes are decomposed into
dyadic blocks. -/
theorem heathBrownZetaPrefixSum_eq_interval
    (A : Nat) (t : Real) :
    heathBrownZetaPrefixSum A t =
      heathBrownZetaIntervalSum 0 (A + 1) t := by
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · intro n hn
    rfl

/-- The inner polynomial in the frozen Fourier-deweighting theorem is exactly
the named zeta prefix, including its sign and both endpoints. -/
theorem typeISourceSmoothBlock_fourierDeweight_zetaPrefix
    (Y A r : Nat) (sigma t : Real) (hY : 0 < Y) :
    typeISourceSmoothBlock Y A r sigma t =
      ∫ xi : Real, 𝓕 (typeILogWeightSchwartz Y A r sigma hY) xi *
        heathBrownZetaPrefixSum A (t - 2 * Real.pi * xi) := by
  simpa only [heathBrownZetaPrefixSum] using
    typeISourceSmoothBlock_fourierDeweight Y A r sigma t hY

/-- The stronger interior-source identity also has the exact named zeta
prefix as its inner polynomial.  In particular, the only exterior scale
factor remains the source-required `Q^(-sigma)`. -/
theorem typeISourceSmoothBlock_eq_interior_zetaPrefix
    {Y A r : Nat} {sigma t : Real} (hY : 0 < Y)
    (hLower : ((Y + 1 : Nat) : Real) ≤ (((2 ^ r * Y : Nat) : Real) / 2))
    (hUpper : (2 * (2 ^ r * Y : Nat) : Nat) ≤ A) :
    typeISourceSmoothBlock Y A r sigma t =
      ((((2 ^ r * Y : Nat) : Real) ^ (-sigma) : Real) : Complex) *
        ∫ xi : Real, 𝓕 (typeIInteriorLogProfileSchwartz sigma) xi *
          Complex.exp
            (-(((2 * Real.pi * xi * Real.log (2 ^ r * Y : Nat) : Real) :
              Complex) * Complex.I)) *
            heathBrownZetaPrefixSum A (t - 2 * Real.pi * xi) := by
  simpa only [heathBrownZetaPrefixSum] using
    typeISourceSmoothBlock_eq_interior_fourier_deweight
      hY hLower hUpper

#print axioms heathBrownZetaIntervalSum_dyadic
#print axioms heathBrownZetaIntervalSum_dyadic_neg
#print axioms heathBrownZetaPrefixSum_eq_interval
#print axioms typeISourceSmoothBlock_fourierDeweight_zetaPrefix
#print axioms typeISourceSmoothBlock_eq_interior_zetaPrefix

end

end GafniTao
