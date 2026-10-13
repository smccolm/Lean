import Dubon2026.OriginalSUnitKummerCharacterMap
import Dubon2026.OriginalSUnitLocalPowerMap
import Dubon2026.OriginalKummerCoordinateLocalization

/-! # The exact kernel of the original selected S-unit local-power map

The selected local integer-unit map and the already surjective original
Kummer character map have the same kernel on the same original S-units.
The proof constructs roots in the actual full S-unit Kummer field and
uses its actual selected prime stabilizers. This removes the kernel
comparison assumption from DUB-17's selected local-unit image calculation.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) (hp : 0 < p)
  (hroot : (primitiveRoots p K).Nonempty)

/-- The actual full S-unit Kummer field, retaining the original radical
field definition and the original ambient inclusion. -/
abbrev OriginalSUnitKummerField := originalKummerRadicalField (Ω := Ω) p
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) p).range)

local notation "N" => OriginalSUnitKummerField K Ω S p

omit [IsGalois K Ω] in
/-- The actual S-unit character is trivial on a subgroup exactly when
its original Kummer root is fixed by that original subgroup. -/
theorem originalSUnitKummerCharacterMap_mem_ker_iff_fixed
    (H : Subgroup Gal(N/K)) (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (β : Nˣ) (hβ : β ^ p = Units.map (algebraMap K N).toMonoidHom x.val) :
    x ∈ (originalSUnitKummerCharacterMap K Ω S p hp hroot H).ker ↔
      (β : N) ∈ IntermediateField.fixedField H := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ hσ
    have he := DFunLike.congr_fun h (⟨σ, hσ⟩ : H)
    rw [originalSUnitKummerCharacterMap_apply K Ω S p hp hroot H x β hβ] at he
    exact congrArg Units.val (div_eq_one.mp he)
  · intro h
    apply MonoidHom.ext
    intro σ
    rw [originalSUnitKummerCharacterMap_apply K Ω S p hp hroot H x β hβ]
    apply div_eq_one.mpr
    apply Units.ext
    exact h σ.val σ.property

/-- The actual selected local-unit power map has exactly the kernel of
the surjective original S-unit Kummer character map on the same subgroup. -/
theorem originalSUnitSelectedPowerMap_ker_eq
    (H : Subgroup Gal(N/K)) (r : ℕ)
    (e : H ≃* (Fin r → Multiplicative (ZMod p)))
    (w : Fin r → HeightOneSpectrum (𝓞 N))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : T = Finset.univ.image (fun i => originalFinitePrimeBelow K N (w i)))
    (hST : Disjoint S T)
    (hD : ∀ i, OriginalFiniteDecompositionGroup K N (w i) =
      Subgroup.zpowers (primeCoordinateGenerator e i).val) :
    (originalSUnitLocalPowerMap K p S T hST).ker =
      (originalSUnitKummerCharacterMap K Ω S p hp hroot H).ker := by
  letI : FiniteDimensional K N :=
    numberField_sUnit_kummerField_finiteDimensional K Ω S S.finite_toSet p hp hroot
  letI : NumberField N := NumberField.of_module_finite K N
  letI : IsGalois K N := originalKummerRadicalField_isGalois p _
  ext x
  let Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) p).range
  obtain ⟨β, hβ⟩ := originalKummerRadicalField_exists_root (Ω := Ω) p hp Δ
    (⟨x.val, (show (S : Set (HeightOneSpectrum (𝓞 K))).unit K ≤ Δ from le_sup_left) x.property⟩ : Δ)
  have hβ' : (β : N) ^ p = algebraMap K N (x.val : K) := congrArg Units.val hβ
  rw [originalSUnitLocalPowerMap_mem_ker_iff K p hp.ne' S T hST x,
    originalSUnitKummerCharacterMap_mem_ker_iff_fixed K Ω S p hp hroot H x β hβ,
    ← originalLocalKummer_coordinates_iff_fixed K N p hp hroot.choose
      (isPrimitiveRoot_of_mem_primitiveRoots hroot.choose_spec) r H e w hD x.val β hβ']
  constructor
  · intro h i
    have hi : originalFinitePrimeBelow K N (w i) ∈ T := by
      rw [hT]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact h ⟨_, hi⟩
  · rintro h ⟨v, hv⟩
    have hSub : T ⊆ Finset.univ.image (fun i => originalFinitePrimeBelow K N (w i)) := hT.le
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hSub hv)
    subst v
    exact h i

end
end Dubon2026
