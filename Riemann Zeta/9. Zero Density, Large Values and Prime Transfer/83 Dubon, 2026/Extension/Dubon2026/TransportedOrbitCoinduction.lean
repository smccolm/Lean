import Dubon2026.TransportedProductRepresentation
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Actual transported orbit factors and their stabilizer cohomology

For a transitive original place orbit, the existing adjunction map from
transported coordinates to coinduction is bijective. Applying the existing
Shapiro isomorphism identifies its cohomology with that of the actual
stabilizer acting on the original completion factor. This discharges the
orbit comparison needed for DUB-17's supported-idele cohomology formula.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))
  [MulAction.IsPretransitive G ι] (i : ι)

/-- The original transported evaluation/coinduction morphism is bijective on a transitive orbit. -/
theorem transportedCoindHom_bijective :
    Function.Bijective (transportedCoindHom R G ι M T T_one T_mul i).hom := by
  constructor
  · intro x y he
    funext j
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G j i
    have h := congrArg (fun f => f.val g) he
    change transportedPiMap R G ι M T g x i = transportedPiMap R G ι M T g y i at h
    rw [transportedPiMap_apply R G ι M T g x j i hg,
      transportedPiMap_apply R G ι M T g y j i hg] at h
    exact (T g j i hg).injective h
  · intro f
    choose k hk using fun j : ι => MulAction.exists_smul_eq G j i
    let x : ∀ j, M j := fun j => (T (k j) j i (hk j)).symm (f.val (k j))
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext g
    let j := g⁻¹ • i
    have hg : g • j = i := smul_inv_smul g i
    have hk' : (k j)⁻¹ • i = j := by rw [← hk j, inv_smul_smul]
    let a := g * (k j)⁻¹
    have ha : a • i = i := by rw [mul_smul, hk', hg]
    have hak : (a * k j) • j = i := by rw [mul_smul, hk j, ha]
    change transportedPiMap R G ι M T g x i = f.val g
    rw [transportedPiMap_apply R G ι M T g x j i hg]
    change T g j i hg ((T (k j) j i (hk j)).symm (f.val (k j))) = f.val g
    calc
      _ = T a i i ha (T (k j) j i (hk j)
          ((T (k j) j i (hk j)).symm (f.val (k j)))) := by
        simpa only [a, inv_mul_cancel_right] using
          T_mul a (k j) j i i (hk j) ha hak
            ((T (k j) j i (hk j)).symm (f.val (k j)))
      _ = T a i i ha (f.val (k j)) := by rw [LinearEquiv.apply_symm_apply]
      _ = f.val g := by
        have hf := f.property ⟨a, ha⟩ (k j)
        change f.val (a * k j) = T a i i ha (f.val (k j)) at hf
        simpa only [a, inv_mul_cancel_right] using hf.symm

/-- The actual transported product on a transitive orbit is the original coinduced stabilizer representation. -/
def transportedOrbitCoindIso :
    transportedPiRep R G ι M T T_one T_mul ≅
      Rep.coind (MulAction.stabilizer G i).subtype
        (transportedStabilizerRep R G ι M T T_one T_mul i) := by
  apply Rep.mkIso
  refine Representation.Equiv.mk
    (LinearEquiv.ofBijective (transportedCoindHom R G ι M T T_one T_mul i).hom.toLinearMap
      (transportedCoindHom_bijective R G ι M T T_one T_mul i)) ?_
  exact (transportedCoindHom R G ι M T T_one T_mul i).hom.isIntertwining'

/-- Existing Shapiro computes the cohomology of the actual transported orbit using its actual stabilizer factor. -/
def transportedOrbitCohomologyIso (n : ℕ) :
    groupCohomology (transportedPiRep R G ι M T T_one T_mul) n ≅
      groupCohomology (transportedStabilizerRep R G ι M T T_one T_mul i) n :=
  (groupCohomology.functor R G n).mapIso (transportedOrbitCoindIso R G ι M T T_one T_mul i) ≪≫
    groupCohomology.coindIso (transportedStabilizerRep R G ι M T T_one T_mul i) n

/-- The original orbit comparison retains the transported evaluation formula. -/
theorem transportedOrbitCoindIso_hom_apply (x : ∀ j, M j) (g : G) :
    ((transportedOrbitCoindIso R G ι M T T_one T_mul i).hom.hom x).val g =
      T g (g⁻¹ • i) i (smul_inv_smul g i) (x (g⁻¹ • i)) := rfl

end
end Dubon2026
