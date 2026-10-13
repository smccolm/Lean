/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Basic

/-! # A finite actual support containing the absolutely ramified primes

Adapted from ClassFieldTheory, commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
AlgebraicNumberTheory/Ramification/FiniteRamifiedPrimes (Apache-2.0).
Only the required finiteness over the integers is retained. Outside this
support, an actual integer uniformizer will discharge the last local
H1/H2 hypotheses in DUB-17's original idele Herbrand formula.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Only finitely many original finite places of a number field ramify over the integers. -/
theorem original_finite_absolutely_ramified_places
    (L : Type) [Field L] [NumberField L] :
    {w : HeightOneSpectrum (𝓞 L) | ¬ Algebra.IsUnramifiedAt ℤ w.asIdeal}.Finite := by
  exact (Ideal.finite_factors (R := 𝓞 L) (I := differentIdeal ℤ (𝓞 L))
    (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 L))).subset (by
      intro w hw
      exact (dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 L) (P := w.asIdeal)).mpr hw)

end
end Dubon2026
