import Dubon2026.AdelicSublevelFiniteSpan
import Dubon2026.AdelicLevelFamilyFaithful
import Dubon2026.ModularFiniteDimension

/-! # A faithful finite family of genuine classical restrictions at an actual adelic sublevel -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The literal real restriction after translating by the chosen representative of each actual finite-level coset. -/
def adelicSublevelClassicalFamily (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    adelicAlgebraicSublevelFiniteSpan f L →ₗ[ℂ]
      ((finiteAdeleGL2Gamma0 N) ⧸ L → SL(2, ℝ) → ℂ) :=
  LinearMap.pi (fun q => ((adelicCyclicRealRestriction f).comp
    ((adelicLiftCyclicRepresentation N k f).toRepresentation
      (rationalAdelicFiniteGL2Embedding (Quotient.out q).val))).domRestrict
        (adelicAlgebraicSublevelFiniteSpan f L))

/-- Zero in every actual coset component forces the original adelic function itself to vanish everywhere. -/
theorem adelicSublevelClassicalFamily_eq_zero
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) (v : adelicAlgebraicSublevelFiniteSpan f L)
    (hv : adelicSublevelClassicalFamily f L v = 0) : v = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply adelicFunction_level_family_eq_zero N v.val.val
    (adelicLiftCyclic_rational_invariant N f v.val.property)
    (adelicLiftCyclic_scalar_invariant N f v.val.property)
  intro a g
  have he := congrFun (congrArg Subtype.val
    (adelicAlgebraicSublevelFiniteSpan_coset_out f L v a)) (adelicRealSL2Embedding g)
  have hz := congrFun (congrFun hv (QuotientGroup.mk a)) g
  exact he.symm.trans hz

/-- The finite-coset real restriction family is faithful on the genuine original sublevel-fixed core. -/
theorem adelicSublevelClassicalFamily_injective (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    Function.Injective (adelicSublevelClassicalFamily f L) := by
  intro v w he
  have hz : adelicSublevelClassicalFamily f L (v - w) = 0 := by
    rw [(adelicSublevelClassicalFamily f L).map_sub v w, he, sub_self]
  exact sub_eq_zero.mp (adelicSublevelClassicalFamily_eq_zero f L (v - w) hz)

/-- Actual cusp forms for the genuine finite-index integral sublevel map to their literal real lifts. -/
def sublevelCuspRealWeightLiftLinear (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    CuspForm ((finiteAdelicSublevelIntegerGroup N L).map (mapGL ℝ)) k →ₗ[ℂ] (SL(2, ℝ) → ℂ) where
  toFun F := realWeightLiftLinear k F
  map_add' F G := (realWeightLiftLinear k).map_add F G
  map_smul' c F := (realWeightLiftLinear k).map_smul c F

/-- Every actual component of the finite-coset family is the lift of a genuine cusp form at the original integral sublevel. -/
theorem adelicSublevelClassicalFamily_mem_cusp_range
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) [L.Normal]
    (v : adelicAlgebraicSublevelFiniteSpan f L) (q : (finiteAdeleGL2Gamma0 N) ⧸ L) :
    adelicSublevelClassicalFamily f L v q ∈ (sublevelCuspRealWeightLiftLinear (k := k) L).range := by
  have h := adelicAlgebraicSublevelFiniteSpan_invariant f L (Quotient.out q) v.val v.property
  obtain ⟨F, hF⟩ := adelicAlgebraicFiniteSpan_sublevel_classical_cusp f L _ h.1 h.2
  exact ⟨F, hF⟩

/-- Genuine finite-index classical cusp-space finiteness and the faithful actual finite-coset family prove finite dimensionality of the original sublevel-fixed finite-adelic core. -/
instance adelicAlgebraicSublevelFiniteSpan_finiteDimensional
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) [L.Normal] [L.FiniteIndex] :
    FiniteDimensional ℂ (adelicAlgebraicSublevelFiniteSpan f L) := by
  letI := finiteAdelicSublevelIntegerGroup_finiteIndex N L
  letI := ModularDimension.cuspForm_finiteDimensional (finiteAdelicSublevelIntegerGroup N L) k
  let T : adelicAlgebraicSublevelFiniteSpan f L →ₗ[ℂ]
      ((finiteAdeleGL2Gamma0 N) ⧸ L → (sublevelCuspRealWeightLiftLinear (k := k) L).range) :=
    LinearMap.pi (fun q =>
      ((LinearMap.proj q).comp (adelicSublevelClassicalFamily f L)).codRestrict _
        (fun v => adelicSublevelClassicalFamily_mem_cusp_range f L v q))
  have hT : Function.Injective T := by
    intro v w he
    apply adelicSublevelClassicalFamily_injective f L
    funext q
    exact congrArg Subtype.val (congrFun he q)
  exact FiniteDimensional.of_injective T hT

end
end Dubon2026
