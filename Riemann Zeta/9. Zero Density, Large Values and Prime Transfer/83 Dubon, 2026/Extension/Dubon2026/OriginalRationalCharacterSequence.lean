import Dubon2026.OriginalRationalCharacterDuality
import Dubon2026.OriginalInternalHomShortExact

/-! # The original integral, rational and rational-circle sequence

This is the literal coefficient sequence used to relate DUB-17's
degree-one character duality to integral degree-two cohomology. Its
exactness is proved from the actual quotient by the integer subgroup;
internal Hom exactness reuses the proved projective lifting theorem.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (G : Type) [Group G]

/-- The actual integer inclusion into the trivial rational coefficient. -/
def originalIntegerRationalInclusion : Rep.trivial ℤ G ℤ ⟶ Rep.trivial ℤ G ℚ :=
  Rep.ofHom ⟨(Int.castAddHom ℚ).toIntLinearMap, fun _ => by ext; rfl⟩

/-- The actual quotient of the rational coefficient by its integer subgroup. -/
def originalRationalCharacterProjection :
    Rep.trivial ℤ G ℚ ⟶ Rep.trivial ℤ G (AddCircle (1 : ℚ)) :=
  Rep.ofHom ⟨(QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap,
    fun _ => by ext; rfl⟩

/-- The original integer-to-rational-to-rational-circle short complex. -/
def originalRationalCharacterShortComplex : ShortComplex (Rep ℤ G) where
  X₁ := Rep.trivial ℤ G ℤ
  X₂ := Rep.trivial ℤ G ℚ
  X₃ := Rep.trivial ℤ G (AddCircle (1 : ℚ))
  f := originalIntegerRationalInclusion G
  g := originalRationalCharacterProjection G
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro n
    change ((n : ℚ) : AddCircle (1 : ℚ)) = 0
    exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨n, by simp⟩

/-- The literal integer and rational-circle coefficient sequence is short exact. -/
theorem originalRationalCharacter_shortExact :
    (originalRationalCharacterShortComplex G).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun x y h => Int.cast_injective h)
    epi_g := (Rep.epi_iff_surjective _).mpr QuotientAddGroup.mk_surjective }
  apply ((originalRationalCharacterShortComplex G).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ G) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  ext x
  change ℚ at x
  constructor
  · rintro ⟨n, rfl⟩
    change ℤ at n
    change ((n : ℚ) : AddCircle (1 : ℚ)) = 0
    exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨n, by simp⟩
  · intro hx
    change (x : AddCircle (1 : ℚ)) = 0 at hx
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp hx
    exact ⟨n, by simpa using hn⟩

/-- The actual lattice Hom sequence is short exact, with no exactness certificate supplied. -/
theorem originalRationalCharacterInternalHom_shortExact
    (M : Rep.{0} ℤ G) [Module.Projective ℤ M] :
    ((originalRationalCharacterShortComplex G).map (Rep.ihom M)).ShortExact :=
  originalInternalHom_shortExact M (originalRationalCharacter_shortExact G)

end
end Dubon2026
