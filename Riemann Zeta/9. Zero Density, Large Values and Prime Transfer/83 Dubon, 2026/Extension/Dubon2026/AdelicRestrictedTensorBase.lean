import Dubon2026.AdelicFiniteReferenceCore

/-! # The genuine fixed real-and-bad-place base for a restricted tensor construction -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The actual good finite places of the original level. -/
abbrev AdelicGoodPlace (N : ℕ) := {v : HeightOneSpectrum ℤ // IsGoodAdelicPlace N v}

/-- The genuine fixed base subgroup has identity at every original good finite coordinate. -/
def adelicRestrictedBaseGroup (N : ℕ) : Subgroup RationalAdelicGL2 :=
  adelicFiniteFamilyAwayGroup (fun v : AdelicGoodPlace N => v.val)

/-- Every actual base matrix has identity at each original good coordinate. -/
theorem adelicRestrictedBaseGroup_place {N : ℕ} (a : adelicRestrictedBaseGroup N)
    (v : HeightOneSpectrum ℤ) (hv : IsGoodAdelicPlace N v) : adelicPlaceGL2Hom v a.val = 1 :=
  adelicFiniteFamilyAwayGroup_place (fun w : AdelicGoodPlace N => w.val) a ⟨v, hv⟩

/-- The same genuine fixed base belongs to every actual finite good-place complement. -/
theorem adelicRestrictedBaseGroup_le_finiteAway {N n : ℕ} (v : Fin n → HeightOneSpectrum ℤ)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    adelicRestrictedBaseGroup N ≤ adelicFiniteFamilyAwayGroup v := by
  intro a ha
  funext i
  exact adelicRestrictedBaseGroup_place ⟨a, ha⟩ (v i) (hgood i)

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual fixed-base action is the original adelic representation restricted to its genuine subgroup. -/
def adelicRestrictedBaseRepresentation : Representation ℂ (adelicRestrictedBaseGroup N) (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp (adelicRestrictedBaseGroup N).subtype

/-- The fixed-base factor is the actual normalized original cusp orbit span under the genuine real-and-bad-place subgroup. -/
def adelicRestrictedBaseCore : Submodule ℂ (AdelicCyclicHilbert f) :=
  Submodule.span ℂ (Set.range (fun a : adelicRestrictedBaseGroup N =>
    adelicRestrictedBaseRepresentation f a (adelicCyclicUnitReference f)))

/-- The genuine fixed-base core inherits the original Hilbert inner product. -/
instance adelicRestrictedBaseCoreInner : InnerProductSpace ℂ (adelicRestrictedBaseCore f) :=
  @Submodule.innerProductSpace ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicRestrictedBaseCore f)

/-- The actual original normalized base orbit, retained as a vector in its genuine algebraic core. -/
def adelicRestrictedBaseOrbit (a : adelicRestrictedBaseGroup N) : adelicRestrictedBaseCore f :=
  ⟨adelicRestrictedBaseRepresentation f a (adelicCyclicUnitReference f), Submodule.subset_span ⟨a, rfl⟩⟩

/-- The actual normalized base orbit spans its entire genuine base factor. -/
theorem adelicRestrictedBaseOrbit_span :
    Submodule.span ℂ (Set.range (adelicRestrictedBaseOrbit f)) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff (adelicRestrictedBaseCore f) _).mpr rfl

variable {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ)

/-- The original fixed base is included as the same actual matrices in every selected finite complement. -/
def adelicRestrictedBaseToFiniteAway (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    adelicRestrictedBaseGroup N →* adelicFiniteFamilyAwayGroup v :=
  Subgroup.inclusion (adelicRestrictedBaseGroup_le_finiteAway v hgood)

/-- The original fixed-base factor lies in the actual complementary core for every finite family of good places. -/
theorem adelicRestrictedBaseCore_le_finiteAway (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    adelicRestrictedBaseCore f ≤ adelicFiniteFamilyAwayCore f v :=
  representationSubgroupOrbitSpan_mono (adelicCyclicHilbertRepresentation f) (adelicCyclicUnitReference f)
    (adelicRestrictedBaseGroup_le_finiteAway v hgood)

/-- Inclusion of the identical original fixed-base vectors preserves their genuine Hilbert norm. -/
def adelicRestrictedBaseCoreInclusion (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    adelicRestrictedBaseCore f →ₗᵢ[ℂ] adelicFiniteFamilyAwayCore f v where
  toLinearMap := Submodule.inclusion (adelicRestrictedBaseCore_le_finiteAway f v hgood)
  norm_map' _ := rfl

/-- The genuine fixed-base inclusion preserves every literal original normalized orbit vector. -/
theorem adelicRestrictedBaseCoreInclusion_orbit (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a : adelicRestrictedBaseGroup N) :
    adelicRestrictedBaseCoreInclusion f v hgood (adelicRestrictedBaseOrbit f a) =
      adelicFiniteFamilyAwayOrbit f v (adelicRestrictedBaseToFiniteAway v hgood a) := by
  apply Subtype.ext
  rfl

end
end Dubon2026
