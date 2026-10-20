import Dubon2026.NumberFieldIntegralFiniteAdelesCompact
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-! # The actual compact open integral finite-adelic matrix level

For the source unitary levels in DUB-17, both a matrix and its inverse
must be integral at every original finite place. Native submonoid-unit
topology turns the proved compact open integral adele ring into exactly
this original compact open matrix subgroup.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField RestrictedProduct

variable (K ι : Type*) [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]

/-- The original matrices and inverses integral at every original finite place. -/
def numberFieldIntegralMatrixLevel :
    Subgroup (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ :=
  ((numberFieldIntegralFiniteAdeles K).matrix (n := ι)).toSubmonoid.units

/-- The integral matrix level has precisely the original entrywise integrality conditions. -/
theorem numberFieldIntegralMatrixLevel_mem_iff
    (M : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) :
    M ∈ numberFieldIntegralMatrixLevel K ι ↔
      (∀ i j v, M.val i j v ∈ v.adicCompletionIntegers K) ∧
      (∀ i j v, (M⁻¹).val i j v ∈ v.adicCompletionIntegers K) := Iff.rfl

/-- The original integral matrix level is open. -/
theorem numberFieldIntegralMatrixLevel_isOpen :
    IsOpen (numberFieldIntegralMatrixLevel K ι :
      Set (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) := by
  apply Submonoid.isOpen_units
  change IsOpen {M : Matrix ι ι (FiniteAdeleRing (𝓞 K) K) |
    ∀ i j, M i j ∈ numberFieldIntegralFiniteAdeles K}
  simp_rw [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact (numberFieldIntegralFiniteAdeles_isOpen K).preimage (continuous_apply_apply i j)

/-- The original integral matrix level is compact. -/
theorem numberFieldIntegralMatrixLevel_isCompact :
    IsCompact (numberFieldIntegralMatrixLevel K ι :
      Set (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) := by
  letI : T2Space (FiniteAdeleRing (𝓞 K) K) := inferInstanceAs
    (T2Space (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]))
  apply Submonoid.units_isCompact
  change IsCompact {M : ι → ι → FiniteAdeleRing (𝓞 K) K |
    ∀ i j, M i j ∈ numberFieldIntegralFiniteAdeles K}
  convert isCompact_univ_pi (fun _ : ι =>
    isCompact_univ_pi fun _ : ι => numberFieldIntegralFiniteAdeles_isCompact K) using 1
  ext M
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const, SetLike.mem_coe]

end
end Dubon2026
