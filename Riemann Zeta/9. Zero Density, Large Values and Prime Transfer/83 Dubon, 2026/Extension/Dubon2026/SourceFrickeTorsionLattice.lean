import Dubon2026.SourceFrickeTorsionTransformationV2
import Dubon2026.SourcePeriodWeierstrassSeparation

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
characters -> Picard/H1 and diamond comparison -> differential realization
-> rational Fourier structure -> faithful Fricke generators.
Reuse the existing actual period homomorphism and its exact lattice kernel,
together with the native elliptic-point x-coordinate theorem. This avoids
a new low-Fourier-coefficient case analysis and assumes no separation result. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceEllipticPeriod
open scoped Manifold MatrixGroups ModularForm PeriodPair

theorem torsion_lift_mem_lattice_iff {N : ℕ} [NeZero N] (τ : ℍ) (u v : ℤ) :
    ((u : ℂ) * τ + v) / N ∈ (periodPairOfTau τ).lattice ↔
      (u : ZMod N) = 0 ∧ (v : ZMod N) = 0 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hm
    obtain ⟨m, n, he⟩ := PeriodPair.mem_lattice.mp hm
    simp only [periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one] at he
    have hc : (((N : ℤ) * m - u : ℤ) : ℂ) * τ +
        (((N : ℤ) * n - v : ℤ) : ℂ) = 0 := by
      push_cast
      have he' := (eq_div_iff hN).mp he
      linear_combination he'
    have hlin := (LinearIndependent.pair_iff.mp (periodPairOfTau τ).indep)
      (((N : ℤ) * m - u : ℤ) : ℝ) (((N : ℤ) * n - v : ℤ) : ℝ)
      (by simpa only [periodPairOfTau_ω₁, periodPairOfTau_ω₂, Complex.real_smul,
        Complex.ofReal_intCast, mul_one] using hc)
    have h₁ : (N : ℤ) * m - u = 0 := by exact_mod_cast hlin.1
    have h₂ : (N : ℤ) * n - v = 0 := by exact_mod_cast hlin.2
    exact ⟨⟨m, (sub_eq_zero.mp h₁).symm⟩, ⟨n, (sub_eq_zero.mp h₂).symm⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    apply PeriodPair.mem_lattice.mpr
    refine ⟨m, n, ?_⟩
    simp only [periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one, Int.cast_mul,
      Int.cast_natCast]
    field_simp

theorem frickeTorsionPt_notMem {N : ℕ} [NeZero N] (τ : ℍ)
    (a : Fin 2 → ZMod N) (ha : a ≠ 0) :
    frickeTorsionPt N a τ ∉ (periodPairOfTau τ).lattice := by
  intro hm
  have hc := (torsion_lift_mem_lattice_iff τ ((a 0).val : ℤ) ((a 1).val : ℤ)).mp hm
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hc
  apply ha
  funext i
  fin_cases i
  · exact hc.1
  · exact hc.2

theorem frickeTorsionPt_sub_mem_iff {N : ℕ} [NeZero N] (τ : ℍ)
    (a b : Fin 2 → ZMod N) :
    frickeTorsionPt N a τ - frickeTorsionPt N b τ ∈ (periodPairOfTau τ).lattice ↔
      a = b := by
  have he : frickeTorsionPt N a τ - frickeTorsionPt N b τ =
      ((((a 0).val : ℤ) - (b 0).val : ℤ) * (τ : ℂ) +
        (((a 1).val : ℤ) - (b 1).val : ℤ)) / N := by
    unfold frickeTorsionPt
    push_cast
    ring
  rw [he, torsion_lift_mem_lattice_iff]
  simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_eq_zero]
  exact ⟨fun hc => funext fun i => by fin_cases i; exact hc.1; exact hc.2,
    fun hc => ⟨congrFun hc 0, congrFun hc 1⟩⟩

theorem frickeTorsionPt_add_mem_iff {N : ℕ} [NeZero N] (τ : ℍ)
    (a b : Fin 2 → ZMod N) :
    frickeTorsionPt N a τ + frickeTorsionPt N b τ ∈ (periodPairOfTau τ).lattice ↔
      a = -b := by
  have he : frickeTorsionPt N a τ + frickeTorsionPt N b τ =
      ((((a 0).val : ℤ) + (b 0).val : ℤ) * (τ : ℂ) +
        (((a 1).val : ℤ) + (b 1).val : ℤ)) / N := by
    unfold frickeTorsionPt
    push_cast
    ring
  rw [he, torsion_lift_mem_lattice_iff]
  simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val,
    ← eq_neg_iff_add_eq_zero]
  exact ⟨fun hc => funext fun i => by fin_cases i; exact hc.1; exact hc.2,
    fun hc => ⟨congrFun hc 0, congrFun hc 1⟩⟩

end
end Dubon2026.SourceFricke
