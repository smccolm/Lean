import Dubon2026.FiniteAbelianGaloisRadicalGeneration
import Dubon2026.SUnitFiniteSupport
import Dubon2026.OriginalKummerRadicalField

/-! # A prescribed finite abelian extension lies in an actual full S-unit radical field

Actual Hilbert-90 coefficients have finite original support. Enlarging
the prescribed S by that support places every generating radical in the
constructed full S-unit field. No radical-generation or support hypothesis
is added. This supplies the containment needed for the restriction map
in DUB-17's global Kummer preparation and cyclic norm-index argument.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField IsMulCommutative
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

/-- Every prescribed finite abelian exponent-n extension is contained in a full S-unit
radical field after a finite enlargement of any prescribed original set of places. -/
theorem finiteAbelian_exists_sUnit_kummer_containment
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (hexp : ∀ g : Gal(E/K), g ^ n = 1)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      E ≤ originalKummerRadicalField (Ω := Ω) n
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range) := by
  classical
  obtain ⟨a, β, hp, _, hgenerate⟩ := finiteAbelianGalois_exists_generating_radicals n hn hζ hexp
  letI : Fintype (Gal(E/K) →* Kˣ) := Fintype.ofFinite _
  obtain ⟨T, hT⟩ := exists_finite_sUnit_support (R := 𝓞 K) (Finset.univ.image a)
  let S := S₀ ∪ T
  let N := originalKummerRadicalField (Ω := Ω) n
    ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)
  refine ⟨S, Finset.subset_union_left, ?_⟩
  have hroots (χ : Gal(E/K) →* Kˣ) : ((β χ).val : Ω) ∈ N := by
    have haT := hT (a χ) (Finset.mem_image.mpr ⟨χ, Finset.mem_univ _, rfl⟩)
    have haS : a χ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K := by
      intro v hv
      exact haT v (fun hvT => hv (Finset.mem_union_right S₀ hvT))
    apply IntermediateField.subset_adjoin K
    have hle : (S : Set (HeightOneSpectrum (𝓞 K))).unit K ≤
        (S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔
          (powMonoidHom (α := Kˣ) n).range := le_sup_left
    refine ⟨⟨a χ, hle haS⟩, ?_⟩
    exact congrArg (fun z : Eˣ => (z.val : Ω)) (hp χ)
  have htop : (⊤ : IntermediateField K E) ≤ N.comap E.val := by
    rw [← hgenerate]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨χ, rfl⟩
    exact hroots χ
  intro x hx
  exact htop (show (⟨x, hx⟩ : E) ∈ (⊤ : IntermediateField K E) from trivial)

end
end Dubon2026
