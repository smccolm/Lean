import Dubon2026.OriginalIntegralPrimeCoinvariants
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # A proved linear section of original prime-torsion coinvariants

Both the original coefficient and its actual coinvariants are vector
spaces over the prime field. Pinned projective lifting splits their
literal quotient map. This removes the linear-section input from the
actual coinduced comparison on DUB-17's integral projectivity route.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2

/-- The actual prime-torsion coefficient's coinvariant projection has an integral linear section, derived by prime-field projective lifting. -/
theorem originalPrimeCoinvariant_exists_linear_section
    {G : Type} [Group G] (A : Rep.{0} ℤ G) (p : ℕ) [Fact p.Prime]
    (hp : ∀ x : A, p • x = 0) :
    ∃ T : A.ρ.Coinvariants →ₗ[ℤ] A,
      ∀ c, Representation.Coinvariants.mk A.ρ (T c) = c := by
  haveI : Module (ZMod p) A := AddCommGroup.zmodModule hp
  have hpC (c : A.ρ.Coinvariants) : p • c = 0 := by
    obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective A.ρ c
    rw [← map_nsmul, hp, map_zero]
  haveI : Module (ZMod p) A.ρ.Coinvariants := AddCommGroup.zmodModule hpC
  let q : A →ₗ[ZMod p] A.ρ.Coinvariants :=
    (Representation.Coinvariants.mk A.ρ).toAddMonoidHom.toZModLinearMap p
  obtain ⟨T₀, hT₀⟩ := Module.projective_lifting_property q
    (LinearMap.id : A.ρ.Coinvariants →ₗ[ZMod p] A.ρ.Coinvariants)
    (Representation.Coinvariants.mk_surjective A.ρ)
  let T : A.ρ.Coinvariants →ₗ[ℤ] A := {
    toFun := T₀
    map_add' := T₀.map_add
    map_smul' := fun m c => by
      simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul T₀ ℤ ℤ m c }
  exact ⟨T, fun c => LinearMap.congr_fun hT₀ c⟩

end
end Dubon2026
