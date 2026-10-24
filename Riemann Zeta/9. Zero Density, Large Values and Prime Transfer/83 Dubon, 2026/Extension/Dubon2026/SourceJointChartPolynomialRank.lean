import Dubon2026.SourceJointChartPolynomialIndependence

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap -> chart
basis rank. Separately supported residue-field bases stay polynomially
independent after multiplication by nonzero coordinate polynomials.
The proved monic chart multiples will put these vectors in the actual
chart, bounding its polynomial rank from below. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly

theorem polynomial_unique_single_multiples
    {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] (Fb : ι → Type*)
    [∀ i, Field (Fb i)] [∀ i, Algebra k (Fb i)] (x : ∀ i, Fb i)
    (hx : ∀ i, Transcendental k (x i)) (d : ι → ℕ)
    (b : ∀ i, Fin (d i) → Fb i)
    (hb : ∀ i, LinearIndependent (IntermediateField.adjoin k ({x i} : Set (Fb i))) (b i))
    (c : (Σ i, Fin (d i)) → k[X]) (hc : ∀ τ, c τ ≠ 0) :
    ∀ q q' : (Σ i, Fin (d i)) → k[X],
      ∑ τ, aeval x (q τ) * (aeval x (c τ) * Pi.single τ.1 (b τ.1 τ.2)) =
        ∑ τ, aeval x (q' τ) * (aeval x (c τ) * Pi.single τ.1 (b τ.1 τ.2)) → q = q' := by
  classical
  letI (i : ι) : Module k[X] (Fb i) := Module.compHom (Fb i) (aeval (x i)).toRingHom
  have hbi : ∀ i, LinearIndependent k[X] (b i) := by
    intro i
    rw [Fintype.linearIndependent_iff]
    intro q hq j
    let a : Fin (d i) → IntermediateField.adjoin k ({x i} : Set (Fb i)) := fun j =>
      ⟨aeval (x i) (q j), IntermediateField.algebra_adjoin_le_adjoin k _
        (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨q j, rfl⟩)⟩
    have he : ∑ j, a j • b i j = 0 := hq
    have hzero := congrArg Subtype.val ((Fintype.linearIndependent_iff.mp (hb i)) a he j)
    exact (transcendental_iff_injective.mp (hx i)) (hzero.trans (map_zero _).symm)
  have hli := Pi.linearIndependent_single (R := k[X]) b hbi
  have hbase : ∀ q q' : (Σ i, Fin (d i)) → k[X],
      ∑ τ, aeval x (q τ) * Pi.single τ.1 (b τ.1 τ.2) =
        ∑ τ, aeval x (q' τ) * Pi.single τ.1 (b τ.1 τ.2) → q = q' := by
    intro q q' he
    apply _root_.funext
    apply Fintype.linearIndependent_iffₛ.mp hli q q'
    have heval : ∀ (p : k[X]) (y : ∀ i, Fb i),
        p • y = aeval x p * y := fun p y => by
      funext i
      change aeval (x i) p * y i = aeval x p i * y i
      rw [aeval_pi_apply₂]
    simpa only [heval] using he
  intro q q' he
  have he' := hbase (fun τ => q τ * c τ) (fun τ => q' τ * c τ) (by
    simpa only [map_mul, mul_assoc] using he)
  exact funext fun τ => mul_right_cancel₀ (hc τ) (congrFun he' τ)

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
