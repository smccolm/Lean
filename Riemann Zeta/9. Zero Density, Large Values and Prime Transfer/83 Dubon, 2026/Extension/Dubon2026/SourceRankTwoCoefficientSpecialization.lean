import Dubon2026.CanonicalAdelicGL2Coordinates
import Mathlib.LinearAlgebra.Pi

/-! DUB-17/18 -> primitive rank-two arithmetic representation -> apply
the proved coefficient character. Native GL2 coefficient change preserves
the group law; the existing GL2 continuity theorem and native matrix-vector
coefficient identity retain continuity and the original vector action. -/
namespace Dubon2026
noncomputable section
open Matrix
variable {K T E : Type*} [CommRing K] [CommRing T] [CommRing E]
variable [Algebra K T] [Algebra K E] (κ : T →ₐ[K] E)

/-- Apply the actual coefficient character to both rank-two coordinates. -/
def rankTwoCoefficientMap : (Fin 2 → T) →ₗ[K] (Fin 2 → E) :=
  κ.toLinearMap.compLeft (Fin 2)

theorem rankTwoCoefficientMap_smul (t : T) (y : Fin 2 → T) :
    rankTwoCoefficientMap κ (t • y) = κ t • rankTwoCoefficientMap κ y := by
  ext i
  exact map_mul κ t (y i)

theorem rankTwoCoefficientMap_span {V : Type*} [AddCommMonoid V] [Module K V]
    (e : V ≃ₗ[K] (Fin 2 → T)) :
    Submodule.span E (Set.range fun x => rankTwoCoefficientMap κ (e x)) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun E (Fin 2)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨e.symm (Pi.single i 1), ?_⟩
  change rankTwoCoefficientMap κ (e (e.symm (Pi.single i 1))) = _
  rw [e.apply_symm_apply]
  ext j
  simp [rankTwoCoefficientMap, Pi.basisFun_apply, Pi.single_apply]

variable {G : Type*} [Group G] (ρ : G →* GeneralLinearGroup (Fin 2) T)

/-- The original invertible rank-two matrices after the prescribed coefficient specialization. -/
def rankTwoCoefficientGaloisRep : G →* GeneralLinearGroup (Fin 2) E :=
  (GeneralLinearGroup.map κ.toRingHom).comp ρ

theorem rankTwoCoefficientGaloisRep_action (g : G) (y : Fin 2 → T) :
    (rankTwoCoefficientGaloisRep κ ρ g).val *ᵥ rankTwoCoefficientMap κ y =
      rankTwoCoefficientMap κ ((ρ g).val *ᵥ y) := by
  ext i
  exact (RingHom.map_mulVec κ.toRingHom (ρ g).val y i).symm

theorem rankTwoCoefficientGaloisRep_continuous
    [TopologicalSpace T] [TopologicalSpace E] [TopologicalSpace G]
    (hκ : Continuous κ) (hρ : Continuous ρ) :
    Continuous (rankTwoCoefficientGaloisRep κ ρ) :=
  (gl2Map_continuous κ.toRingHom hκ).comp hρ

end
end Dubon2026
