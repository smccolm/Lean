import Dubon2026.FiniteAbelianGaloisRadicalGeneration
import Dubon2026.SUnitFiniteSupport
import Dubon2026.OriginalSUnitSelectedKernel

/-! # Kummer enlargement of the literal original prime-degree field

The existing original radical generators are mapped through the actual
ambient algebra tower. Their finite coefficient support puts the entire
original field inside the actual S-unit Kummer field. The resulting algebra
embedding retains the original upper field itself; no transported idele or
class-norm space is introduced. This supplies the shorter same-field route
from the proved principal localization to DUB-17's original norm index for
arbitrary finite prime-degree extensions.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField Classical IsMulCommutative
variable (K L Ω : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]

/-- A finite original support supplies an actual algebra embedding of the
literal prime-degree field into the original full S-unit Kummer field. -/
theorem original_primeDegree_sUnit_kummer_embedding
    (p : ℕ) [Fact p.Prime] (hDegree : Module.finrank K L = p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      Nonempty (L →ₐ[K] OriginalSUnitKummerField K Ω S p) := by
  have hp : p.Prime := Fact.out
  have hroot : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  have hCard : Nat.card Gal(L/K) = p := (IsGalois.card_aut_eq_finrank K L).trans hDegree
  letI : IsCyclic Gal(L/K) := isCyclic_of_prime_card hCard
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  have hPower (g : Gal(L/K)) : g ^ p = 1 := by
    rw [← hCard]
    exact pow_card_eq_one' (x := g)
  obtain ⟨a, β, hβ, _, hGenerate⟩ :=
    finiteAbelianGalois_exists_generating_radicals p hp.pos hroot hPower
  letI : Fintype (Gal(L/K) →* Kˣ) := Fintype.ofFinite _
  obtain ⟨T, hT⟩ := exists_finite_sUnit_support (R := 𝓞 K) (Finset.univ.image a)
  let S := S₀ ∪ T
  let N := OriginalSUnitKummerField K Ω S p
  let j : L →ₐ[K] Ω := IsScalarTower.toAlgHom K L Ω
  have hRoots (χ : Gal(L/K) →* Kˣ) : j ((β χ).val) ∈ N := by
    have haT := hT (a χ) (Finset.mem_image.mpr ⟨χ, Finset.mem_univ _, rfl⟩)
    have haS : a χ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K := by
      intro v hv
      exact haT v (fun hvT => hv (Finset.mem_union_right S₀ hvT))
    apply IntermediateField.subset_adjoin K
    have hle : (S : Set (HeightOneSpectrum (𝓞 K))).unit K ≤
        (S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) p).range := le_sup_left
    refine ⟨⟨a χ, hle haS⟩, ?_⟩
    change j ((β χ).val) ^ p = algebraMap K Ω ((a χ).val)
    rw [← map_pow]
    have hb : (β χ).val ^ p = algebraMap K L ((a χ).val) := congrArg Units.val (hβ χ)
    rw [hb, j.commutes]
  have hTop : (⊤ : IntermediateField K L) ≤ N.comap j := by
    rw [← hGenerate]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨χ, rfl⟩
    exact hRoots χ
  exact ⟨S, Finset.subset_union_left,
    ⟨j.codRestrict N.toSubalgebra (fun x => hTop (show x ∈ (⊤ : IntermediateField K L) from trivial))⟩⟩

end
end Dubon2026
