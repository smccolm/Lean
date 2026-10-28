import Mathlib
import Definitions.Def_TaylorWiles_CyclotomicChar
import Theorems.Thm_MonoidHom_exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient
import P2M.Util
namespace P2MW.S_TaylorWiles_exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues

open NumberField

namespace TWSeedElement

variable {L : Type*} [Field L] [NumberField L]

theorem isCyclic_quotient_ker_cycloChar {m : ℕ} [NeZero m] {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ m)
    (hcyc : IsCyclic (ZMod m)ˣ) :
    IsCyclic ((L ≃ₐ[ℚ] L) ⧸ (TaylorWiles.cycloChar hζ).ker) := by
  haveI : IsCyclic (TaylorWiles.cycloChar hζ).range := Subgroup.isCyclic _
  exact isCyclic_of_surjective
    (QuotientGroup.quotientKerEquivRange (TaylorWiles.cycloChar hζ)).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivRange (TaylorWiles.cycloChar hζ)).symm.surjective

end TWSeedElement

theorem solution
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] {𝕜 : Type*} [Field 𝕜]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (ρ : TaylorWiles.ResidualRep L 𝕜) (n : ℕ)
    {ζ : 𝓞 L} [NeZero (p ^ n)] (hζ : IsPrimitiveRoot ζ (p ^ n))
    (h2 : (2 : 𝕜) ≠ 0)
    (hirr : Submodule.span 𝕜 (Set.range ρ) = ⊤)
    (hsplit : ∀ g : L ≃ₐ[ℚ] L, ∃ a b : 𝕜, (ρ g).trace = a + b ∧ (ρ g).det = a * b) :
    ∃ σ ∈ (TaylorWiles.cycloChar hζ).ker, (ρ σ).HasDistinctRationalEigenvalues := by
  haveI : IsCyclic ((L ≃ₐ[ℚ] L) ⧸ (TaylorWiles.cycloChar hζ).ker) :=
    TWSeedElement.isCyclic_quotient_ker_cycloChar hζ
      (ZMod.isCyclic_units_of_prime_pow p Fact.out hp n)
  obtain ⟨σ, hσ, hdisc⟩ :=
    MonoidHom.exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient h2 ρ hirr
      (TaylorWiles.cycloChar hζ).ker
  obtain ⟨a, b, htr, hdet⟩ := hsplit σ
  refine ⟨σ, hσ, a, b, ?_, htr, hdet⟩
  rintro rfl
  apply hdisc
  rw [htr, hdet]
  ring
