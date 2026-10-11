import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.RingTheory.Localization.Integral

/-! # Integral normal bases for actual full lattices in a Galois field

The integral basis here spans a full lattice, not necessarily the entire
integer ring. A single original denominator scales the genuine normal basis.
-/

namespace Dubon2026
noncomputable section

open scoped nonZeroDivisors

variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]

/-- Scale the actual normal-basis generator by one nonzero original base
denominator. Its whole original Galois orbit is integral and remains a basis. -/
theorem exists_integral_normal_basis :
    ∃ b : Module.Basis Gal(L/K) K L,
      (∀ σ, b σ = σ (b 1)) ∧ ∀ σ, IsIntegral R (b σ) := by
  let b := IsGalois.normalBasis K L
  obtain ⟨r, hr⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Rₘ := K) R⁰ (b 1) (Algebra.IsIntegral.isIntegral (R := K) (b 1))
  have hr0 : algebraMap R K (r : R) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero r.property
      (IsFractionRing.injective R K (h.trans (map_zero _).symm))
  let u : Kˣ := Units.mk0 (algebraMap R K (r : R)) hr0
  let b' : Module.Basis Gal(L/K) K L := u • b
  have horbit (σ : Gal(L/K)) : b' σ = σ (b' 1) := by
    simp only [b', Module.Basis.smul_apply, Units.smul_def, map_smul]
    rw [IsGalois.normalBasis_apply]
  have hint : IsIntegral R (b' 1) := by
    simpa only [b', Module.Basis.smul_apply, Units.smul_def, u,
      Units.val_mk0, algebraMap_smul, Submonoid.smul_def] using hr
  refine ⟨b', horbit, ?_⟩
  intro σ
  rw [horbit σ]
  exact hint.map (σ.restrictScalars R)

omit [IsDomain R] [IsFractionRing R K] [FiniteDimensional K L] [IsGalois K L] in
/-- The lattice spanned over the original base ring by a displayed normal
basis is stable under the actual Galois action. -/
theorem normalBasis_span_galois_stable
    (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
    (σ : Gal(L/K)) {x : L} (hx : x ∈ Submodule.span R (Set.range b)) :
    σ x ∈ Submodule.span R (Set.range b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨τ, rfl⟩ := hx
    have heq : σ (b τ) = b (σ * τ) := by rw [hb τ, hb (σ * τ)]; rfl
    rw [heq]
    exact Submodule.subset_span (Set.mem_range_self (σ * τ))
  | zero => simpa only [map_zero] using (Submodule.span R (Set.range b)).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    change (σ.restrictScalars R) (a • x) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ a hx

end
end Dubon2026
