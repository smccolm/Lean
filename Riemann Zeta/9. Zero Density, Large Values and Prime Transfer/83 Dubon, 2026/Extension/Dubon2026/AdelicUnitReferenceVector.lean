import Dubon2026.AdelicNormalizedCoefficientFactor

/-! # Actual unit reference vectors for coherent original cusp tensor transitions -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- Division by the literal complex-cast norm gives a unit vector whenever the original vector is nonzero. -/
theorem complex_inverse_norm_smul_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (x : V) (hx : x ≠ 0) : ‖(‖x‖ : ℂ)⁻¹ • x‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- The inner product of the genuinely normalized vector with its original translate is exactly the normalized original matrix coefficient. -/
theorem complex_inverse_norm_coefficient {G V : Type*} [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Representation ℂ G V) (x : V) (g : G) :
    inner ℂ ((‖x‖ : ℂ)⁻¹ • x) (ρ g ((‖x‖ : ℂ)⁻¹ • x)) =
      representationNormalizedCoefficient ρ x g := by
  rw [map_smul, inner_smul_left, inner_smul_right, representationNormalizedCoefficient,
    inner_self_eq_norm_sq_to_K]
  rw [map_inv₀, Complex.conj_ofReal, div_eq_mul_inv, ← inv_pow]
  rw [pow_two]
  ac_rfl

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original adelic cusp generator divided by its actual nonzero Hilbert norm. -/
def adelicCyclicUnitReference : AdelicCyclicHilbert f :=
  (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ • adelicCyclicHilbertGenerator f

/-- The actual reference vector of every nonzero original cusp form has unit original Hilbert norm. -/
theorem adelicCyclicUnitReference_norm (hf : f ≠ 0) : ‖adelicCyclicUnitReference f‖ = 1 :=
  @complex_inverse_norm_smul_norm (AdelicCyclicHilbert f) inferInstance inferInstance
    (adelicCyclicHilbertGenerator f) (adelicCyclicHilbertGenerator_ne_zero f hf)

/-- The actual unit reference coefficient is exactly the previously proved normalized original cusp coefficient. -/
theorem adelicCyclicUnitReference_coefficient (a : RationalAdelicGL2) :
    inner ℂ (adelicCyclicUnitReference f)
      (adelicCyclicHilbertRepresentation f a (adelicCyclicUnitReference f)) =
        adelicNormalizedCuspCoefficient f a :=
  @complex_inverse_norm_coefficient RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    (adelicCyclicHilbertGenerator f) a

end
end Dubon2026
