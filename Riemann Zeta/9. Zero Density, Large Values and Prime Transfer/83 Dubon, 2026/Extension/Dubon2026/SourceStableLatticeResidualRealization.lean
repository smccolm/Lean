import Dubon2026.SourceStableLatticeContinuity
import Dubon2026.SourceLocalFieldResidueReduction

/-! DUB-17/18 -> actual residual association -> continuous integral and
residual matrices. A basis is constructed from the proved rank-two
lattice, and its extension supplies the exact comparison with the
original field action. Reduction is the literal residue of every entry. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
open Matrix
variable {E G : Type*} [Field E] [ValuativeRel E] [UniformSpace E]
variable [IsNonarchimedeanLocalField E]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
private local instance : TopologicalSpace 𝓀[E] :=
  inferInstanceAs (TopologicalSpace (𝒪[E] ⧸ IsLocalRing.maximalIdeal 𝒪[E]))

theorem stableLattice_integral_residual_realization
    (ρ : G →* GeneralLinearGroup (Fin 2) E) (hρ : Continuous ρ)
    (L : Submodule 𝒪[E] (Fin 2 → E))
    (hspan : Submodule.span E (L : Set (Fin 2 → E)) = ⊤)
    (hfree : Module.Free 𝒪[E] L) (hfinite : Module.Finite 𝒪[E] L)
    (hrank : Module.finrank 𝒪[E] L = 2)
    (hL : ∀ g x, x ∈ L → (ρ g).val *ᵥ x ∈ L) :
    ∃ (e : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E))
      (ρint : G →* GeneralLinearGroup (Fin 2) 𝒪[E])
      (ρres : G →* GeneralLinearGroup (Fin 2) 𝓀[E]),
      Continuous ρint ∧ Continuous ρres ∧
      (∀ g i j, (ρres g).val i j = IsLocalRing.residue 𝒪[E] ((ρint g).val i j)) ∧
      ∀ g v, (ρint g).val.map (algebraMap 𝒪[E] E) *ᵥ e v = e ((ρ g).val *ᵥ v) := by
  letI := hfree
  letI := hfinite
  letI : Submodule.IsLattice E L := ⟨Module.Finite.iff_fg.mp hfinite, hspan⟩
  let b := Module.finBasisOfFinrankEq 𝒪[E] L hrank
  let ρint := stableLatticeGeneralLinearRep ρ L hL b
  have hc : Continuous ρint := stableLatticeGeneralLinearRep_continuous ρ L hL b hρ
  refine ⟨(b.extendOfIsLattice E).equivFun, ρint, localFieldResidualRep E ρint,
    hc, localFieldResidualRep_continuous E ρint hc, localFieldResidualRep_entry E ρint, ?_⟩
  intro g v
  exact stableLatticeGeneralLinearRep_field_action ρ L hL b g v

end
end Dubon2026
