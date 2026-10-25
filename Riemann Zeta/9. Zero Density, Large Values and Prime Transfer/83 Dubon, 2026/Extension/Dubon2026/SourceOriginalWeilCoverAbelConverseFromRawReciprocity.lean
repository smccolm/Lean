import Dubon2026.SourceOriginalWeilCoverPathIntegralSubtraction
import Dubon2026.SourceOriginalWeilCoverGeneratorPeriodCorrection
import Dubon2026.SourceOriginalWeilCoverIntegralPeriodsFromGenerators
import Dubon2026.SourceOriginalWeilCoverPrescribedResidues

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse. The native integer-period correction and actual cover integral-period principality consume the geometric loop-generation and bilinear/third-kind reciprocity clauses explicitly. These raw geometric clauses remain open, so this is a conditional Abel converse. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential Matrix
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)

/-- The exact raw third-kind reciprocity clause for the actual cover.
This is a geometric input statement, not an existence or Abel-converse proof. -/
def CoverRawThirdKindReciprocity {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE))
    (P₀ : Place ℂ EE) (D : Divisor ℂ EE)
    (Pz : Fin kDim ⊕ Fin kDim → Place ℂ EE) (Z : ∀ k, CoverPath (Pz k) (Pz k))
    (Q : Matrix (Fin kDim ⊕ Fin kDim) (Fin kDim ⊕ Fin kDim) ℤ) : Prop :=
    ∀ η : Ω[EE⁄ℂ], (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η) →
      (∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ)) →
      ∃ κ : Fin kDim ⊕ Fin kDim → ℤ, ∀ i : Fin kDim,
        ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k) *
          pathIntegral N n radicand baseDivisor hRadicand hOrders η (Z l) = 2 * Real.pi * Complex.I *
            (abelJacobiDiv N n radicand baseDivisor hRadicand hOrders (k := kDim) (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) P₀ D i +
              ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k))

theorem cover_isPrincipal_of_raw_reciprocity {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE))
    (P₀ : Place ℂ EE) (D : Divisor ℂ EE) (hD0 : Divisor.degree D = 0)
    (hD : abelJacobiDiv N n radicand baseDivisor hRadicand hOrders (k := kDim) (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) P₀ D ∈
      pathPeriodLattice N n radicand baseDivisor hRadicand hOrders (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])))
    (Pz : Fin kDim ⊕ Fin kDim → Place ℂ EE) (Z : ∀ k, CoverPath (Pz k) (Pz k))
    (Q : Matrix (Fin kDim ⊕ Fin kDim) (Fin kDim ⊕ Fin kDim) ℤ)
    (hZ : ∀ k t, D (Z k t) = 0) (hQ : IsUnit Q.det)
    (hgen : ∀ (P : Place ℂ EE) (γ : CoverPath P P), ∃ κ : Fin kDim ⊕ Fin kDim → ℤ,
      ∀ i, pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) γ =
        ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k))
    (hgenRes : ∀ (P : Place ℂ EE) (γ : CoverPath P P), (∀ t, D (γ t) = 0) →
      ∃ (κ : Fin kDim ⊕ Fin kDim → ℤ) (w : Place ℂ EE → ℤ), ∀ η : Ω[EE⁄ℂ],
        (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η) →
        (∀ v : Place ℂ EE, D v = 0 → 0 ≤ v.ordDifferential η) →
        pathIntegral N n radicand baseDivisor hRadicand hOrders η γ = ∑ k, (κ k : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders η (Z k) +
          2 * Real.pi * Complex.I * ∑ v ∈ D.support,
            (w v : ℂ) * v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η))
    (hRR : ∀ i j : Fin kDim, ∑ k, ∑ l, (Q k l : ℂ) *
      pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (Z k) * pathIntegral N n radicand baseDivisor hRadicand hOrders (b j : Ω[EE⁄ℂ]) (Z l) = 0)
    (hrec : CoverRawThirdKindReciprocity N n radicand baseDivisor hRadicand hOrders b P₀ D Pz Z Q) :
    Divisor.IsPrincipal D := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  obtain ⟨η, hηr⟩ := exists_cover_third_kind_differential N n radicand D hD0
  have hη := fun v => (hηr v).1
  have hres := fun v => (hηr v).2
  have hcor := exists_cover_generator_period_correction N n radicand baseDivisor hRadicand hOrders b P₀ D η hD
    Pz Z Q hQ hgen hRR (hrec η hη hres)
  obtain ⟨ζ, hζ, m, hm⟩ := hcor
  have hζreg : ∀ v : Place ℂ EE, v.differentialCoeff ζ ∈ v.toValuationSubring :=
    fun v => v.mem_of_ord_nonneg
      ((mem_cover_regularDifferentials_iff_ord_nonneg N n radicand ζ).mp hζ v)
  have hm' : ∀ k, pathIntegral N n radicand baseDivisor hRadicand hOrders (η - ζ) (Z k) = 2 * Real.pi * Complex.I * (m k : ℂ) := by
    intro k
    rw [pathIntegral_sub_of_coeff_mem N n radicand baseDivisor hRadicand hOrders η ζ (Z k)
      (fun t => cover_coeff_regular_off_divisor N n radicand D η hη hres (Z k t) (hZ k t))
      (fun t => hζreg (Z k t)), hm]
  have hθ := cover_simple_poles_sub_regular N n radicand η ζ hη hζ
  have hθres := cover_residues_sub_regular N n radicand D η ζ hη hres hζ
  exact cover_isPrincipal_of_integral_periods N n radicand baseDivisor hRadicand hOrders D (η - ζ) hθ hθres
    (cover_integral_periods_of_generators N n radicand baseDivisor hRadicand hOrders D (η - ζ) hθ hθres Pz Z m hm' hgenRes)


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
