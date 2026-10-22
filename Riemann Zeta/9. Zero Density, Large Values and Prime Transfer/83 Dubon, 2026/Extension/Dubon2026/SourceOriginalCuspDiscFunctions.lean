import Dubon2026.SourceOriginalNormalizedCuspDisc
import Dubon2026.SourceCuspDiscGermUniqueness

/-! DUB-17/18 -> original torsion cardinality -> actual cusp place chart.
Choose the already proved common-disk realizations for the actual
normalized cusp embedding. Connected meromorphic uniqueness transports
the original field operations to punctured germs at every disk point.
These functions will supply the valuation laws for the actual cusp chart.
-/
namespace Dubon2026.SourceFunctionField.CuspLabels
noncomputable section
open CuspTaylor Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N] (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
variable (s : {s // s ∈ labels N})

/-- The proved common positive radius for the normalized original cusp embedding. -/
def discRadius : ℝ := (original_normalized_cusp_common_disc N ζ hζ s).choose

theorem discRadius_pos : 0 < discRadius N ζ hζ s :=
  (original_normalized_cusp_common_disc N ζ hζ s).choose_spec.1

/-- The actual selected meromorphic realization of an original function on the common disk. -/
def discRealize (f : modularFunctionFieldOver N ℂ) : ℂ → ℂ :=
  ((original_normalized_cusp_common_disc N ζ hζ s).choose_spec.2 f).choose

theorem discRealize_meromorphicOn (f : modularFunctionFieldOver N ℂ) :
    MeromorphicOn (discRealize N ζ hζ s f) (ball 0 (discRadius N ζ hζ s)) :=
  ((original_normalized_cusp_common_disc N ζ hζ s).choose_spec.2 f).choose_spec.1

theorem discRealize_represents (f : modularFunctionFieldOver N ℂ) :
    Represents (normalizedEmbedding N ζ hζ s f) (discRealize N ζ hζ s f) :=
  ((original_normalized_cusp_common_disc N ζ hζ s).choose_spec.2 f).choose_spec.2.1

theorem discRealize_order_zero (f : modularFunctionFieldOver N ℂ) (hf : f ≠ 0) :
    meromorphicOrderAt (discRealize N ζ hζ s f) 0 = ((place N ℂ ζ hζ s).ord f : WithTop ℤ) :=
  ((original_normalized_cusp_common_disc N ζ hζ s).choose_spec.2 f).choose_spec.2.2.1 hf

theorem discRealize_order_ne_top (f : modularFunctionFieldOver N ℂ) (hf : f ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s)) :
    meromorphicOrderAt (discRealize N ζ hζ s f) z ≠ ⊤ :=
  ((original_normalized_cusp_common_disc N ζ hζ s).choose_spec.2 f).choose_spec.2.2.2 hf z hz

theorem discRealize_const (c : ℂ) {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s)) :
    discRealize N ζ hζ s (algebraMap ℂ (modularFunctionFieldOver N ℂ) c) =ᶠ[𝓝[≠] z]
      (fun _ => c) := by
  have hc := represents_const c
  rw [← (normalizedEmbedding N ζ hζ s).commutes] at hc
  exact (discRealize_represents N ζ hζ s _).eventuallyEq_on_disc
    (discRadius_pos N ζ hζ s) (discRealize_meromorphicOn N ζ hζ s _) (MeromorphicOn.const c) hc hz

theorem discRealize_add (f g : modularFunctionFieldOver N ℂ)
    {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s)) :
    discRealize N ζ hζ s (f + g) =ᶠ[𝓝[≠] z]
      discRealize N ζ hζ s f + discRealize N ζ hζ s g := by
  have hfg := (discRealize_represents N ζ hζ s f).add (discRealize_represents N ζ hζ s g)
  rw [← map_add] at hfg
  exact (discRealize_represents N ζ hζ s _).eventuallyEq_on_disc
    (discRadius_pos N ζ hζ s) (discRealize_meromorphicOn N ζ hζ s _)
    ((discRealize_meromorphicOn N ζ hζ s f).add (discRealize_meromorphicOn N ζ hζ s g)) hfg hz

theorem discRealize_mul (f g : modularFunctionFieldOver N ℂ)
    {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s)) :
    discRealize N ζ hζ s (f * g) =ᶠ[𝓝[≠] z]
      discRealize N ζ hζ s f * discRealize N ζ hζ s g := by
  have hfg := (discRealize_represents N ζ hζ s f).mul (discRealize_represents N ζ hζ s g)
  rw [← map_mul] at hfg
  exact (discRealize_represents N ζ hζ s _).eventuallyEq_on_disc
    (discRadius_pos N ζ hζ s) (discRealize_meromorphicOn N ζ hζ s _)
    ((discRealize_meromorphicOn N ζ hζ s f).mul (discRealize_meromorphicOn N ζ hζ s g)) hfg hz

theorem discRealize_inv (f : modularFunctionFieldOver N ℂ)
    {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s)) :
    discRealize N ζ hζ s f⁻¹ =ᶠ[𝓝[≠] z] (discRealize N ζ hζ s f)⁻¹ := by
  have hfg := (discRealize_represents N ζ hζ s f).inv
  rw [← map_inv₀] at hfg
  exact (discRealize_represents N ζ hζ s _).eventuallyEq_on_disc
    (discRadius_pos N ζ hζ s) (discRealize_meromorphicOn N ζ hζ s _)
    (discRealize_meromorphicOn N ζ hζ s f).inv hfg hz

end
end Dubon2026.SourceFunctionField.CuspLabels
