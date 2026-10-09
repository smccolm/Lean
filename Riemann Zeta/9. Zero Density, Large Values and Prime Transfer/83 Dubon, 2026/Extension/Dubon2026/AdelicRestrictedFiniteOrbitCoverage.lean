import Dubon2026.AdelicRestrictedTensorChain
import Dubon2026.AdelicGoodLevelBaseDecomposition

/-! # Every original adelic cusp orbit vector is represented at a genuine finite tensor stage -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

/-- Removing a sufficiently long genuine good-place initial family leaves original local level at every good place. -/
theorem adelicInitialRemoval_exists_good_level (N : ℕ) [NeZero N] (a : RationalAdelicGL2) :
    ∃ n, ∀ v, IsGoodAdelicPlace N v →
      adelicPlaceGL2Hom v (adelicFinitePlaceRemoval (goodAdelicPlaceInitial N n)
        (goodAdelicPlaceInitial_injective N n) a) ∈ finitePlaceGL2Gamma0 N v := by
  classical
  obtain ⟨S, hS⟩ := finiteAdeleGL2Gamma0_exists_exceptional_finset N (rationalAdelicGL2RealFiniteEquiv a).2
  obtain ⟨n, hn⟩ := goodAdelicPlaceInitial_covers_finset N S
  refine ⟨n, ?_⟩
  intro v hv
  by_cases hm : ∃ i : Fin n, goodAdelicPlaceInitial N n i = v
  · obtain ⟨i, rfl⟩ := hm
    rw [adelicFinitePlaceRemoval_same]
    exact (finitePlaceGL2Gamma0 N _).one_mem
  · rw [adelicFinitePlaceRemoval_ne _ _ v (fun i hi => hm ⟨i, hi.symm⟩)]
    exact hS v (fun hvS => hm (hn v hvS hv))

variable {N : ℕ} [NeZero N] {k : ℤ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The normalized original cusp reference is fixed by the actual finite level group. -/
theorem adelicCyclicUnitReference_finite_level (u : finiteAdeleGL2Gamma0 N) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding u.val)
      (adelicCyclicUnitReference f) = adelicCyclicUnitReference f := by
  rw [adelicCyclicUnitReference, map_smul, adelicCyclicHilbertGenerator_finite_level]

variable (F : PrimitiveCuspForm N k)

/-- Every genuine original adelic unit-reference orbit vector is the image of an actual finite good-place/fixed-base pure tensor. -/
theorem adelicRestrictedStageIsometry_covers_original_orbit (a : RationalAdelicGL2) :
    ∃ n x, adelicRestrictedStageIsometry F n x =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicCyclicUnitReference F.toCuspForm) := by
  obtain ⟨n, hn⟩ := adelicInitialRemoval_exists_good_level N a
  obtain ⟨b, u, hbu⟩ := adelicGoodLevel_exists_base_mul_level N
    (adelicFinitePlaceRemoval (goodAdelicPlaceInitial N n) (goodAdelicPlaceInitial_injective N n) a) hn
  let g := fun i => adelicPlaceGL2Hom (goodAdelicPlaceInitial N n i) a
  refine ⟨n, adelicRestrictedFiniteTensorFamily F.toCuspForm (goodAdelicPlaceInitial N n) (g, b), ?_⟩
  change adelicRestrictedFiniteTensorIsometry (goodAdelicPlaceInitial N n) F
    (goodAdelicPlaceInitial_injective N n) (goodAdelicPlaceInitial_good N n)
    (adelicRestrictedFiniteTensorFamily F.toCuspForm (goodAdelicPlaceInitial N n) (g, b)) = _
  have himage := adelicRestrictedFiniteTensorIsometry_family (goodAdelicPlaceInitial N n) F
    (goodAdelicPlaceInitial_injective N n) (goodAdelicPlaceInitial_good N n) (g, b)
  have he : (adelicFinitePlaceProduct (goodAdelicPlaceInitial N n) (goodAdelicPlaceInitial_injective N n) g * b.val) *
      rationalAdelicFiniteGL2Embedding u.val = a := by
    rw [mul_assoc, hbu]
    exact adelicFinitePlaceProduct_mul_removal (goodAdelicPlaceInitial N n) (goodAdelicPlaceInitial_injective N n) a
  have hu : adelicCyclicHilbertRepresentation F.toCuspForm
      ((adelicFinitePlaceProduct (goodAdelicPlaceInitial N n) (goodAdelicPlaceInitial_injective N n) g * b.val) *
        rationalAdelicFiniteGL2Embedding u.val) (adelicCyclicUnitReference F.toCuspForm) =
      adelicCyclicHilbertRepresentation F.toCuspForm
        (adelicFinitePlaceProduct (goodAdelicPlaceInitial N n) (goodAdelicPlaceInitial_injective N n) g * b.val)
        (adelicCyclicUnitReference F.toCuspForm) := by
    rw [map_mul, Module.End.mul_apply, adelicCyclicUnitReference_finite_level]
  exact himage.trans (hu.symm.trans (congrArg (fun c : RationalAdelicGL2 =>
    adelicCyclicHilbertRepresentation F.toCuspForm c (adelicCyclicUnitReference F.toCuspForm)) he))

end
end Dubon2026
