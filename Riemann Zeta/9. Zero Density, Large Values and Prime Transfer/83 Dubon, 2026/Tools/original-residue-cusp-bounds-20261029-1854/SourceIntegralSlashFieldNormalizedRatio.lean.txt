import Dubon2026.SourceIntegralSlashFieldEmbedding

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> second full-base coordinate in the actual cusp
chart. The needed raised E4-cube/discriminant ratio has weight twelve. Prove
its map formula using the already constructed normalized generators and field
operations, with no separate general all-weight cusp embedding construction. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm
local notation "Zbar" => integralClosure ℤ ℂ
variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] {K : Type*} [Field K] [CharP K ℓ]
  (φ : Zbar →+* K) (hN : (N : K) ≠ 0)
private local instance : Algebra K (qExpFunctionFieldC K (Gamma1 N)) :=
  (qExpFunctionFieldC K (Gamma1 N)).toSubalgebra.algebra
include ℓ

theorem originalReducedSlashFieldHom_normalized_ratio (β : SL(2, ℤ))
    (Φ : qExpFunctionFieldC K (Gamma1 N) →ₐ[K] LaurentSeries K)
    (hΦ : ∀ x (hx : x ∈ normalizedGenerators N K),
      Φ ⟨x, normalizedGenerators_subset N K hx⟩ = normalizedSlashValue N φ hN β x)
    {r : ℕ} (f g : ModularForm (Gamma1 N) (12 * (r : ℤ))) {p q : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) (hq : IsIntegralQExp g q) (hq0 : intSeriesC K q ≠ 0) :
    Φ ⟨intSeriesC K p / intSeriesC K q, div_mem_qExpFunctionFieldC f g hp hq hq0⟩ =
      HahnSeries.ofPowerSeries ℤ K (reducedSlashSeries N
        ((show Even (12 : ℤ) by decide).mul_right (r : ℤ)) f hp β φ hN) /
      HahnSeries.ofPowerSeries ℤ K (reducedSlashSeries N
        ((show Even (12 : ℤ) by decide).mul_right (r : ℤ)) g hq β φ hN) := by
  let d := intSeriesC K discriminantSeries
  let x : qExpFunctionFieldC K (Gamma1 N) :=
    ⟨intSeriesC K p / d ^ r, normalizedGenerators_subset N K ⟨r, f, p, hp, rfl⟩⟩
  let y : qExpFunctionFieldC K (Gamma1 N) :=
    ⟨intSeriesC K q / d ^ r, normalizedGenerators_subset N K ⟨r, g, q, hq, rfl⟩⟩
  have he : (⟨intSeriesC K p / intSeriesC K q,
      div_mem_qExpFunctionFieldC f g hp hq hq0⟩ : qExpFunctionFieldC K (Gamma1 N)) = x / y := by
    apply Subtype.ext
    exact (div_div_div_cancel_right₀ (pow_ne_zero r (intSeriesC_discriminant_ne_zero K)) _ _).symm
  have hx := hΦ (intSeriesC K p / d ^ r) ⟨r, f, p, hp, rfl⟩
  have hy := hΦ (intSeriesC K q / d ^ r) ⟨r, g, q, hq, rfl⟩
  change Φ x = _ at hx
  change Φ y = _ at hy
  rw [he, map_div₀, hx, hy, normalizedSlashValue_eq N φ hN β ℓ f hp rfl,
    normalizedSlashValue_eq N φ hN β ℓ g hq rfl,
    div_div_div_cancel_right₀ (pow_ne_zero r (reducedSlashSeries_discriminant_ne_zero N φ hN β))]

end
end Dubon2026.SourceFunctionField.IntegralSlash
