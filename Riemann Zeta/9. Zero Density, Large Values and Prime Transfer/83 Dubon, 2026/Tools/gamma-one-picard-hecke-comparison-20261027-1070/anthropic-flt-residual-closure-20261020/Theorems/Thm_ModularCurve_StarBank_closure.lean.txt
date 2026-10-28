import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_StarBank_closure

open ModularCurve
theorem ModularCurve.StarBank.closure {K : Type*} [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) {M : ℕ} {G R : Polynomial K}
    (hstar : Polynomial.aeval (jqModC K) G *
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1)
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p)
    (hpress : R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
        ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))))
    (hnorm : (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
      qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
    HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
      qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^
        (p + 1)) :
    ∃ c : K, c ≠ 0 ∧ G.comp R ∣ Polynomial.C c * G ^ (p + 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_StarBank_closure.solution
