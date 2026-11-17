import Dubon2026.SourceGroupAlgebraQuotientSpan

/-! DUB-17/18 -> original rank-two realization -> actual trace algebra.
Construct an algebra and a genuine group action in its units from the
proved trace identities. Its trace pairing and scalar idempotent corners
are proved. Finite dimension two and matrix realization are not assumed
or claimed by this intermediate construction. -/
namespace Dubon2026
noncomputable section

/-- The original dimension-two trace identities construct a genuine
trace algebra with a faithful trace pairing, scalar trace-one corners and the actual group-image
spanning property needed for later matrix continuity. -/
theorem exists_spanning_algebra_of_trace_determinant
    {G R : Type} [Group G] [CommRing R] (t : G → R) (D : G →* R)
    (hOne : t 1 = 2) (hCyc : ∀ g h, t (g * h) = t (h * g))
    (hProd : ∀ g h, t g * t h = t (g * h) + t (g * h⁻¹) * D h) :
    ∃ (A : Type) (_ : Ring A) (_ : Algebra R A) (T : A →ₗ[R] R) (ρ : G →* Aˣ),
      T 1 = 2 ∧ (∀ g, T (ρ g : A) = t g) ∧
      (∀ x y, T (x * y) = T (y * x)) ∧
      (∀ x, (∀ y, T (x * y) = 0) → x = 0) ∧
      (∀ x y, x * y + y * x - T x • y - T y • x +
        (T x * T y - T (x * y)) • (1 : A) = 0) ∧
      (∀ e : A, e * e = e → T e = 1 → ∀ x, e * x * e = T (e * x) • e) ∧
      Submodule.span R (Set.range (fun g => (ρ g : A))) = ⊤ := by
  let τ := sourceGroupTrace t
  have hc : ∀ x y, τ (x * y) = τ (y * x) := sourceGroupTrace_cyclic t hCyc
  let I := sourceTraceRadical τ hc
  let A := MonoidAlgebra R G ⧸ I
  let T : A →ₗ[R] R := sourceTraceQuotientLinear τ hc
  let ρ : G →* Aˣ :=
    ((Ideal.Quotient.mk I).toMonoidHom.comp (MonoidAlgebra.of R G)).toHomUnits
  have ht (g : G) : T (ρ g : A) = t g := sourceGroupTrace_of t g
  have hp : ∀ x y : A, x * y + y * x - T x • y - T y • x +
      (T x * T y - T (x * y)) • (1 : A) = 0 :=
    sourceTraceQuotient_polarized τ hc (sourceGroupTrace_trilinear t D hCyc hProd)
  refine ⟨A, inferInstance, inferInstance, T, ρ, ?_, ht,
    sourceTraceQuotientLinear_cyclic τ hc, sourceTraceQuotientLinear_nondegenerate τ hc,
    hp, (fun e he hte x => traceOneIdempotent_corner_scalar T hp e he hte x),
    sourceGroupAlgebraQuotient_span I⟩
  simpa only [map_one, Units.val_one, hOne] using ht 1

end
end Dubon2026
