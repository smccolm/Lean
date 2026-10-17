import Dubon2026.OriginalInternalHomScalarReduction
import Mathlib.Algebra.Module.Projective

/-! # Exact scalar reduction of the actual internal Hom

Original maps with zero reduction divide linearly by the nonzero scalar
in the torsion-free target. Projectivity of the integral source lifts
every map between the literal reductions. These give the actual short
exact sequence used to prove integral internal-Hom H1 vanishing and
split the fundamental free kernel's cover on DUB-17's duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (A R : Rep.{0} k G) (m : k)

/-- An original map whose literal scalar reduction vanishes is an actual scalar multiple when the target is torsion free. -/
theorem originalInternalHomReduction_kernel
    [IsDomain k] [Module.IsTorsionFree k R] (hm : m ≠ 0)
    (φ : A →ₗ[k] R) (hφ : originalInternalHomReductionLinear A R m φ = 0) :
    ∃ ψ : A →ₗ[k] R, m • ψ = φ := by
  let L := (originalScalarMultiplication R m).hom.toLinearMap
  have hi : Function.Injective L :=
    (Rep.mono_iff_injective _).mp (originalScalarReduction_shortExact R m hm).mono_f
  have hmem (a : A) : φ a ∈ LinearMap.range L := by
    have he := LinearMap.congr_fun hφ ((originalScalarImage A m).mkQ a)
    change (originalScalarImage R m).mkQ (φ a) = 0 at he
    exact (Submodule.Quotient.mk_eq_zero _).mp he
  let ψ : A →ₗ[k] R := (LinearEquiv.ofInjective L hi).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range L) φ hmem
  refine ⟨ψ, LinearMap.ext fun a => ?_⟩
  have he : L (ψ a) = φ a :=
    congrArg Subtype.val ((LinearEquiv.ofInjective L hi).apply_symm_apply ⟨φ a, hmem a⟩)
  change m • ψ a = φ a
  exact (originalScalarMultiplication_apply R m (ψ a)).symm.trans he

/-- Projectivity of the original source lifts every actual map between the literal scalar reductions. -/
theorem originalInternalHomReduction_surjective [Module.Projective k A] :
    Function.Surjective (originalInternalHomReductionLinear A R m) := by
  intro χ
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property (originalScalarImage R m).mkQ
    (χ ∘ₗ (originalScalarImage A m).mkQ) (originalScalarImage R m).mkQ_surjective
  refine ⟨φ, ?_⟩
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro a
  exact LinearMap.congr_fun hφ a

/-- The original internal Hom, multiplication and actual reduction form the literal coefficient complex. -/
def originalInternalHomReductionShortComplex : ShortComplex (Rep k G) where
  X₁ := (Rep.ihom A).obj R
  X₂ := (Rep.ihom A).obj R
  X₃ := (Rep.ihom (originalScalarReduction A m)).obj (originalScalarReduction R m)
  f := originalScalarMultiplication ((Rep.ihom A).obj R) m
  g := originalInternalHomReduction A R m
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro φ
    change originalInternalHomReductionLinear A R m
      ((originalScalarMultiplication ((Rep.ihom A).obj R) m).hom φ) = 0
    rw [originalScalarMultiplication_apply]
    exact originalInternalHomReduction_scalar_zero A R m φ

/-- The actual internal-Hom reduction sequence is short exact for a projective source, torsion-free target and nonzero scalar. -/
theorem originalInternalHomReduction_shortExact
    [IsDomain k] [Module.Projective k A] [Module.IsTorsionFree k R] (hm : m ≠ 0) :
    (originalInternalHomReductionShortComplex A R m).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun φ ψ hφψ => by
      change (originalScalarMultiplication ((Rep.ihom A).obj R) m).hom φ =
        (originalScalarMultiplication ((Rep.ihom A).obj R) m).hom ψ at hφψ
      rw [originalScalarMultiplication_apply, originalScalarMultiplication_apply] at hφψ
      apply LinearMap.ext
      intro a
      exact smul_right_injective R hm (LinearMap.congr_fun hφψ a))
    epi_g := (Rep.epi_iff_surjective _).mpr (originalInternalHomReduction_surjective A R m) }
  apply ((originalInternalHomReductionShortComplex A R m).exact_map_iff_of_faithful
    (forget₂ (Rep k G) (ModuleCat k))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro φ hφ
  change originalInternalHomReductionLinear A R m φ = 0 at hφ
  obtain ⟨ψ, hψ⟩ := originalInternalHomReduction_kernel A R m hm φ hφ
  refine ⟨ψ, ?_⟩
  change (originalScalarMultiplication ((Rep.ihom A).obj R) m).hom ψ = φ
  rw [originalScalarMultiplication_apply]
  exact hψ

end
end Dubon2026
