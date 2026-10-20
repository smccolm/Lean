import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! # The original finite-place projection on finite-adelic invertible matrices

The DUB-17 small-level argument uses one specified finite place. This map
is the pinned restricted-product evaluation, entry by entry.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K ι : Type*) [Field K] [NumberField K]
variable [Fintype ι] [DecidableEq ι]

/-- Projection of the original finite-adelic invertible matrix to a specified finite completion. -/
def numberFieldFiniteAdelicMatrixProjection (v : HeightOneSpectrum (𝓞 K)) :
    (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ →* (Matrix ι ι (v.adicCompletion K))ˣ :=
  Units.map (show FiniteAdeleRing (𝓞 K) K →+* v.adicCompletion K from
    RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v
      ).mapMatrix.toMonoidHom

end
end Dubon2026
