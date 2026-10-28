import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_StarBank_delta_pow_ne

open ModularCurve
theorem ModularCurve.StarBank.delta_pow_ne (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ) (γ : K) :
    (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p ≠
      HahnSeries.C γ * qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_StarBank_delta_pow_ne.solution
