import Dubon2026.SourceCurveTateLeibniz
import Dubon2026.SourceCurveTateCommutatorFinite

/-! The residue Leibniz rule for every actual rational place. The finite
rank of all commutators and all multiplication defects is derived from
the already proved finite principal parts. This is the exact local input
needed to construct the differential factor of the residue pairing. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Multiplication in the field is composition of the literal multiplication operators. -/
theorem tate_lmul_mul (f g : F) :
    Algebra.lmul K F (f * g) = Algebra.lmul K F f ∘ₗ Algebra.lmul K F g := by
  ext x
  exact mul_assoc f g x

/-- The actual local Tate residue satisfies the differential Leibniz rule. -/
theorem tateResidue_leibniz
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g h : F) :
    v.tateResidue f (g * h) = v.tateResidue (f * g) h + v.tateResidue (f * h) g := by
  haveI := v.finite_range_principalPart_mul hres g
  haveI := v.finite_range_principalPart_mul hres h
  haveI := finite_range_epsRestrict v.tateProj (Algebra.lmul K F g) (Algebra.lmul K F h)
  haveI := finite_range_epsRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F g)
  haveI := finite_range_epsRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F h)
  haveI := v.finite_range_tate_commutator hres f h
  haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict v.tateProj
      (Algebra.lmul K F f) (Algebra.lmul K F g ∘ₗ Algebra.lmul K F h))) := by
    rw [← tate_lmul_mul]
    exact v.finite_range_tate_commutator hres f (g * h)
  haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict v.tateProj
      (Algebra.lmul K F f ∘ₗ Algebra.lmul K F g) (Algebra.lmul K F h))) := by
    rw [← tate_lmul_mul]
    exact v.finite_range_tate_commutator hres (f * g) h
  haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict v.tateProj
      (Algebra.lmul K F f ∘ₗ Algebra.lmul K F h) (Algebra.lmul K F g))) := by
    rw [← tate_lmul_mul]
    exact v.finite_range_tate_commutator hres (f * h) g
  unfold tateResidue
  rw [tate_lmul_mul, tate_lmul_mul, tate_lmul_mul]
  exact tateCommTrace_leibniz_snd _ _ _ _

end Dubon2026.SourceCurve.Place
