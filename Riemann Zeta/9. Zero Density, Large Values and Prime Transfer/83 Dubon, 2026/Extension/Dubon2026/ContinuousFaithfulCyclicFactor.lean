import Dubon2026.ContinuousFiniteCharacterCarryInflation
import Dubon2026.ContinuousGaloisFiniteFactors

/-! # Faithful finite cyclic factors of original continuous characters

The actual fixed field of the open character kernel gives the precise finite
stage needed for local cup nondegeneracy. No general reciprocity map is needed.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {n : ℕ}

/-- Every actual continuous finite cyclic character factors faithfully through
the original finite Galois field fixed by its kernel. -/
theorem continuousGaloisCharacter_faithful_cyclic_factor
    (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ψ : Gal(F/K) →* Multiplicative (ZMod n),
        Function.Injective ψ ∧ finiteGaloisCharacterInflation F ψ = χ := by
  let χ₀ := χ.toMonoidHom
  have hopen : IsOpen (χ₀.ker : Set Gal(Ω/K)) :=
    (isOpen_discrete ({1} : Set (Multiplicative (ZMod n)))).preimage χ.continuous
  let H : ClosedSubgroup Gal(Ω/K) := ⟨χ₀.ker, χ₀.ker.isClosed_of_isOpen hopen⟩
  let L := IntermediateField.fixedField χ₀.ker
  have hfix : L.fixingSubgroup = χ₀.ker :=
    InfiniteGalois.fixingSubgroup_fixedField H
  letI : FiniteDimensional K L := by
    apply (InfiniteGalois.isOpen_iff_finite L).mp
    simpa only [hfix] using hopen
  letI : IsGalois K L := by
    apply (InfiniteGalois.normal_iff_isGalois L).mp
    rw [hfix]
    infer_instance
  let F : FiniteGaloisIntermediateField K Ω := {
    toIntermediateField := L
    finiteDimensional := inferInstance
    isGalois := inferInstance }
  let e := InfiniteGalois.normalAutEquivQuotient H
  let ψ : Gal(F/K) →* Multiplicative (ZMod n) :=
    (QuotientGroup.kerLift χ₀).comp e.symm.toMonoidHom
  refine ⟨F, ψ, (QuotientGroup.kerLift_injective χ₀).comp e.symm.injective, ?_⟩
  apply ContinuousMonoidHom.ext
  intro g
  change QuotientGroup.kerLift χ₀
    (e.symm (e (QuotientGroup.mk' χ₀.ker g))) = χ₀ g
  rw [e.symm_apply_apply]
  rfl

end
end Dubon2026
