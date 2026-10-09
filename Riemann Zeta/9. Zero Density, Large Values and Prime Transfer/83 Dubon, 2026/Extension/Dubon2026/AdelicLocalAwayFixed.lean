import Dubon2026.AdelicLocalCyclicCore
import Dubon2026.AdelicSublevelLowestFiniteDimension
import Dubon2026.FiniteAdelicPlaceRemoval
import Dubon2026.ContinuousCyclicScalar

/-! # The genuine local cyclic space retains all original finite-level invariance away from its place -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- An original finite adelic matrix with identity at a place commutes with every genuine single-place matrix there. -/
theorem finiteAdelicLocalGL2_commute_of_place_one (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (ha : GeneralLinearGroup.map (finiteAdelePlace v) a = 1)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    Commute a (finiteAdelicLocalGL2 v g) := by
  apply finiteAdelicGL2_ext
  intro w
  simp only [map_mul]
  by_cases h : w = v
  · subst w
    rw [ha, one_mul, mul_one]
  · rw [finiteAdelicLocalGL2_ne v w h, mul_one, one_mul]

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine single-place cyclic Hilbert space lies in the original finite-adelic cyclic Hilbert space. -/
theorem adelicLocalCyclicClosedSpan_le_finite (v : HeightOneSpectrum ℤ) :
    adelicLocalCyclicClosedSpan f v ≤ adelicFiniteCyclicClosedSpan f := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact Submodule.subset_span ⟨finiteAdelicLocalGL2 v g, rfl⟩

/-- Every original finite-level element supported away from the actual place fixes its whole genuine local cyclic Hilbert space. -/
theorem adelicLocalCyclic_away_fixed (v : HeightOneSpectrum ℤ)
    (a : finiteAdeleGL2Gamma0 N) (ha : GeneralLinearGroup.map (finiteAdelePlace v) a.val = 1)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicClosedSpan f v) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val) x = x := by
  have ho (y : AdelicCyclicHilbert f) : (1 : ℂ) • y = y :=
    @one_smul ℂ (AdelicCyclicHilbert f) inferInstance
      (inferInstance : Module ℂ (AdelicCyclicHilbert f)).toDistribMulAction.toMulAction y
  have hs : adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding a.val) x = (1 : ℂ) • x := by
    apply @continuousLinearMap_scalar_on_closedSpan (AdelicCyclicHilbert f)
      (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) inferInstance inferInstance
      (adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding a.val)) 1
      (fun g => adelicCyclicLocalRepresentation f v g (adelicCyclicHilbertGenerator f))
    · intro g
      have he := ((finiteAdelicLocalGL2_commute_of_place_one v a.val ha g).map
        rationalAdelicFiniteGL2Embedding).map (adelicCyclicHilbertRepresentation f)
      have hh := LinearMap.congr_fun he.eq (adelicCyclicHilbertGenerator f)
      change adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val)
        (adelicCyclicLocalRepresentation f v g (adelicCyclicHilbertGenerator f)) =
        adelicCyclicLocalRepresentation f v g
          (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val)
            (adelicCyclicHilbertGenerator f)) at hh
      rw [adelicCyclicHilbertGenerator_finite_level f a] at hh
      simpa only [ho] using hh
    · exact hx
  simpa only [ho] using hs

/-- On the actual local cyclic Hilbert space, every original finite-level matrix acts precisely by its genuine coordinate at that place. -/
theorem adelicLocalCyclic_level_action (v : HeightOneSpectrum ℤ) (a : finiteAdeleGL2Gamma0 N)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicClosedSpan f v) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val) x =
      adelicCyclicLocalRepresentation f v (GeneralLinearGroup.map (finiteAdelePlace v) a.val) x := by
  have hr : finiteAdelicPlaceRemoval v a.val ∈ finiteAdeleGL2Gamma0 N :=
    finiteAdelicPlaceRemoval_mem_level N v a.val
      (fun w _ => (finiteAdeleGL2Gamma0_iff_places N a.val).mp a.property w)
  have hxfix := adelicLocalCyclic_away_fixed f v ⟨_, hr⟩ (finiteAdelicPlaceRemoval_same v a.val) x hx
  have he := congrArg (fun b => adelicCyclicHilbertRepresentation f
    (rationalAdelicFiniteGL2Embedding b) x) (finiteAdelicLocal_mul_removal v a.val)
  simp only [map_mul, Module.End.mul_apply] at he
  rw [hxfix] at he
  exact he.symm

end
end Dubon2026
