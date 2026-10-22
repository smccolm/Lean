import Dubon2026.SourceOriginalGeneratorPeriodCorrection
import Dubon2026.SourceOriginalIntegralPeriodsFromGenerators
import Dubon2026.SourceOriginalPrescribedResidues

/-! DUB-17/18 -> original torsion cardinality -> full Abel-Jacobi comparison.
Raw geometric loop generation and reciprocity imply the Abel converse on the
actual original curve. Prescribed residues, regular period correction, all-loop
integrality, meromorphic exponential gluing and original-function comparison
are all proved dependencies. The raw geometric clauses remain upstream; this
is not yet an unconditional Abel converse or a closed Dubon acceptance gate.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Matrix
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_isPrincipal_of_raw_reciprocity {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    (P₀ : Place ℂ F) (D : Divisor ℂ F) (hD0 : Divisor.degree D = 0)
    (hD : abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈
      pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])))
    (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (hZ : ∀ k t, D (Z k t) = 0) (hQ : IsUnit Q.det)
    (hgen : ∀ (P : Place ℂ F) (γ : Path P P), ∃ κ : Fin n ⊕ Fin n → ℤ,
      ∀ i, pathIntegral N (b i : Ω[F⁄ℂ]) γ =
        ∑ k, (κ k : ℂ) * pathIntegral N (b i : Ω[F⁄ℂ]) (Z k))
    (hgenRes : ∀ (P : Place ℂ F) (γ : Path P P), (∀ t, D (γ t) = 0) →
      ∃ (κ : Fin n ⊕ Fin n → ℤ) (w : Place ℂ F → ℤ), ∀ η : Ω[F⁄ℂ],
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential η) →
        (∀ v : Place ℂ F, D v = 0 → 0 ≤ v.ordDifferential η) →
        pathIntegral N η γ = ∑ k, (κ k : ℂ) * pathIntegral N η (Z k) +
          2 * Real.pi * Complex.I * ∑ v ∈ D.support,
            (w v : ℂ) * originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η))
    (hRR : ∀ i j : Fin n, ∑ k, ∑ l, (Q k l : ℂ) *
      pathIntegral N (b i : Ω[F⁄ℂ]) (Z k) * pathIntegral N (b j : Ω[F⁄ℂ]) (Z l) = 0)
    (hrec : ∀ η : Ω[F⁄ℂ], (∀ v : Place ℂ F, -1 ≤ v.ordDifferential η) →
      (∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ)) →
      ∃ κ : Fin n ⊕ Fin n → ℤ, ∀ i : Fin n,
        ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral N (b i : Ω[F⁄ℂ]) (Z k) *
          pathIntegral N η (Z l) = 2 * Real.pi * Complex.I *
            (abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ D i +
              ∑ k, (κ k : ℂ) * pathIntegral N (b i : Ω[F⁄ℂ]) (Z k))) :
    Divisor.IsPrincipal D := by
  obtain ⟨η, hηr⟩ := exists_original_third_kind_differential N D hD0
  have hη := fun v => (hηr v).1
  have hres := fun v => (hηr v).2
  obtain ⟨ζ, hζ, m, hm⟩ := exists_original_generator_period_correction N b P₀ D η hD
    Pz Z Q hQ hgen hRR (hrec η hη hres)
  have hζreg : ∀ v : Place ℂ F, v.differentialCoeff ζ ∈ v.toValuationSubring :=
    fun v => v.mem_of_ord_nonneg
      ((mem_original_regularDifferentials_iff_ord_nonneg N ℂ ζ).mp hζ v)
  have hm' : ∀ k, pathIntegral N (η - ζ) (Z k) = 2 * Real.pi * Complex.I * (m k : ℂ) := by
    intro k
    rw [pathIntegral_sub_of_coeff_mem N η ζ (Z k)
      (fun t => original_coeff_regular_off_divisor N D η hη hres (Z k t) (hZ k t))
      (fun t => hζreg (Z k t)), hm]
  have hθ := original_simple_poles_sub_regular N η ζ hη hζ
  have hθres := original_residues_sub_regular N D η ζ hη hres hζ
  exact original_isPrincipal_of_integral_periods N D (η - ζ) hθ hθres
    (original_integral_periods_of_generators N D (η - ζ) hθ hθres Pz Z m hm' hgenRes)

end
end Dubon2026.SourceFunctionField.OriginalChart
