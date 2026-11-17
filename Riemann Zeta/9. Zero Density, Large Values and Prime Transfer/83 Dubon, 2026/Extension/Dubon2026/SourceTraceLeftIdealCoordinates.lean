import Dubon2026.SourceTraceOppositePair
import Dubon2026.AlgebraIdempotentMatrixAction

/-! DUB-17/18 -> actual rank-two realization -> two-vector left-ideal basis.
The opposite pair already constructed from the actual trace pairing
spans the original idempotent left ideal. Its two trace coordinates are
explicit, preparing native basis and matrix-action reuse. -/
namespace Dubon2026
noncomputable section
variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- The original left ideal is spanned by the idempotent and its constructed
opposite partner, with coefficients given by the original trace. -/
theorem traceIdempotent_leftIdeal_expansion (T : A →ₗ[K] K)
    (hCyc : ∀ x y, T (x * y) = T (y * x))
    (hPol : ∀ x y, x * y + y * x - T x • y - T y • x +
      (T x * T y - T (x * y)) • (1 : A) = 0)
    (e b c : A) (he : e * e = e) (hte : T e = 1)
    (heb : e * b = b) (hcb : c * b = 1 - e) (hce : c * e = c)
    (z : A) (hz : z * e = z) :
    z = T z • e + T (b * z) • c := by
  have hez : e * z = T z • e := by
    have h := traceOneIdempotent_corner_scalar T hPol e he hte z
    rw [mul_assoc, hz, hCyc e z, hz] at h
    exact h
  have hbz : b * z = T (b * z) • e := by
    have h := traceOneIdempotent_corner_scalar T hPol e he hte (b * z)
    rw [← mul_assoc e b z, heb, mul_assoc b z e, hz] at h
    exact h
  calc
    z = e * z + c * (b * z) := by rw [← mul_assoc c b z, hcb]; noncomm_ring
    _ = T z • e + T (b * z) • c := by
      conv_lhs => rw [hez, hbz, mul_smul_comm, hce]

/-- The two original trace coordinates recover the coefficients of the
actual idempotent and opposite partner. -/
theorem traceIdempotent_pair_coordinates (T : A →ₗ[K] K)
    (hCyc : ∀ x y, T (x * y) = T (y * x))
    (e b c : A) (hte : T e = 1) (hec : e * c = 0) (hce : c * e = c)
    (hbe : b * e = 0) (hbc : b * c = e) (s t : K) :
    T (s • e + t • c) = s ∧ T (b * (s • e + t • c)) = t := by
  have htc : T c = 0 := by rw [← hce, hCyc, hec, map_zero]
  constructor
  · simp only [map_add, map_smul, hte, htc, smul_eq_mul, mul_one, mul_zero, add_zero]
  · simp only [mul_add, mul_smul_comm, hbe, hbc, smul_zero, zero_add,
      map_smul, hte, smul_eq_mul, mul_one]

end
end Dubon2026
