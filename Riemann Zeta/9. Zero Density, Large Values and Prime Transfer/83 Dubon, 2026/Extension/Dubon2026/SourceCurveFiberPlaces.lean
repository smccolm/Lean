import Dubon2026.SourceCurveFiberChart

/-! DUB-17/18 -> original global residue identity -> normal-closure descent.
The existing prime-place and chart-center constructions give the exact
bijection between extension places over a fixed place and the height-one
primes of its actual integral closure. This is the indexing bridge needed
to transport the pinned Dedekind ramification sum to actual residue fibers.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

instance integralClosureAtConstantsAlgebra (v : Place K F) :
    Algebra K (integralClosureAt E v) :=
  ((algebraMap v.toValuationSubring (integralClosureAt E v)).comp
    (algebraMap K v.toValuationSubring)).toAlgebra

instance integralClosureAtConstantsTower (v : Place K F) :
    IsScalarTower K v.toValuationSubring (integralClosureAt E v) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance integralClosureAtExtensionTower (v : Place K F) :
    IsScalarTower K (integralClosureAt E v) E := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap K E a = algebraMap (integralClosureAt E v) E
    (algebraMap v.toValuationSubring (integralClosureAt E v)
      (algebraMap K v.toValuationSubring a))
  rw [← IsScalarTower.algebraMap_apply v.toValuationSubring (integralClosureAt E v) E,
    IsScalarTower.algebraMap_apply v.toValuationSubring F E,
    ← IsScalarTower.algebraMap_apply K v.toValuationSubring F,
    ← IsScalarTower.algebraMap_apply K F E]

variable (E) in
/-- The existing prime place on the actual integral-closure chart. -/
def fiberPrimePlace (v : Place K F) (P : HeightOneSpectrum (integralClosureAt E v)) :
    Place K E := ofHeightOneSpectrum P

theorem restrict_fiberPrimePlace (v : Place K F)
    (P : HeightOneSpectrum (integralClosureAt E v)) :
    (fiberPrimePlace E v P).restrict F = v := by
  let w := fiberPrimePlace E v P
  have hle : v.toValuationSubring ≤ (w.restrict F).toValuationSubring := by
    intro f hf
    change algebraMap F E f ∈ w.toValuationSubring
    have h := algebraMap_mem_ofHeightOneSpectrum (K := K) (F := E) P
      (algebraMap v.toValuationSubring (integralClosureAt E v) ⟨f, hf⟩)
    rw [← IsScalarTower.algebraMap_apply v.toValuationSubring (integralClosureAt E v) E,
      IsScalarTower.algebraMap_apply v.toValuationSubring F E] at h
    exact h
  exact (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle (w.restrict F).ne_top')).symm

theorem fiberCenter_fiberPrimePlace (v : Place K F)
    (P : HeightOneSpectrum (integralClosureAt E v)) :
    fiberCenter E (restrict_fiberPrimePlace v P) = P := by
  exact centerHeightOneSpectrum_ofHeightOneSpectrum (K := K) (F := E) P

theorem fiberPrimePlace_fiberCenter {v : Place K F} {w : Place K E}
    (hw : w.restrict F = v) : fiberPrimePlace E v (fiberCenter E hw) = w :=
  ofHeightOneSpectrum_center w (integralClosureAt_mem_of_restrict_eq hw)

variable (E) in
/-- The exact correspondence between the actual place fiber and its chart primes. -/
def fiberPrimeEquiv (v : Place K F) :
    {w : Place K E // w.restrict F = v} ≃ HeightOneSpectrum (integralClosureAt E v) where
  toFun w := fiberCenter E w.2
  invFun P := ⟨fiberPrimePlace E v P, restrict_fiberPrimePlace v P⟩
  left_inv w := Subtype.ext (fiberPrimePlace_fiberCenter w.2)
  right_inv P := fiberCenter_fiberPrimePlace v P

end
end Dubon2026.SourceCurve.Place
