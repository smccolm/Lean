import Dubon2026.OriginalPrincipalApproximation
import Dubon2026.NormedFieldUnitPowerOpen
import Dubon2026.OriginalFinitePowerQuotientFinite

/-! # Actual simultaneous principal correction into local powers

The original local degree-power subgroups lie in local norm images. Their
openness and mixed approximation remove every exceptional local obstruction
by one actual principal idele. This is the next input for DUB-17's required
prime-selection and global norm-index upper bound.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- Positive powers form an open subgroup in every actual approximation completion. -/
theorem originalApproximation_power_isOpen
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : 0 < n)
    (i : OriginalApproximationPlace K S) :
    IsOpen ((powMonoidHom n : (OriginalApproximationCompletion K S i)ˣ →*
      (OriginalApproximationCompletion K S i)ˣ).range : Set (OriginalApproximationCompletion K S i)ˣ) := by
  cases i with
  | inl v =>
    let F := v.1.adicCompletion K
    letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (WithZero (Multiplicative ℤ))
    have hnF : (n : F) ≠ 0 := by
      have h := (algebraMap K F).injective.ne (Nat.cast_ne_zero.mpr hn.ne' : (n : K) ≠ 0)
      simpa only [map_natCast, map_zero] using h
    exact normedField_unitPower_range_isOpen F n hnF
  | inr w =>
    have hnorm (x : K) : ‖algebraMap K w.Completion x‖ = w x := by
      exact UniformSpace.Completion.norm_coe ((WithAbs.equiv w.1).symm x)
    obtain ⟨x, hx0, hx1⟩ := w.isNontrivial
    letI : NontriviallyNormedField w.Completion := NontriviallyNormedField.ofNormNeOne (by
      refine ⟨algebraMap K w.Completion x, ?_, ?_⟩
      · simpa only [map_zero] using (algebraMap K w.Completion).injective.ne hx0
      · rw [hnorm]
        exact hx1)
    have hnF : (n : w.Completion) ≠ 0 := by
      have h := (algebraMap K w.Completion).injective.ne (Nat.cast_ne_zero.mpr hn.ne' : (n : K) ≠ 0)
      simpa only [map_natCast, map_zero] using h
    exact normedField_unitPower_range_isOpen w.Completion n hnF

/-- One original global unit corrects all prescribed original local units into positive powers. -/
theorem original_principalUnit_power_approximation
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : 0 < n)
    (a : ∀ i, (OriginalApproximationCompletion K S i)ˣ) :
    ∃ x : Kˣ, ∀ i,
      a i * (Units.map (algebraMap K (OriginalApproximationCompletion K S i)).toMonoidHom x)⁻¹ ∈
        (powMonoidHom n : (OriginalApproximationCompletion K S i)ˣ →*
          (OriginalApproximationCompletion K S i)ˣ).range :=
  original_principalUnit_open_approximation K S a
    (fun i => (powMonoidHom n : (OriginalApproximationCompletion K S i)ˣ →*
      (OriginalApproximationCompletion K S i)ˣ).range)
    (originalApproximation_power_isOpen K S n hn)

end
end Dubon2026
