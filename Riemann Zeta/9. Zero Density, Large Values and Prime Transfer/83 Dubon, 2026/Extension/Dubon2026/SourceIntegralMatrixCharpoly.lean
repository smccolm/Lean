import Dubon2026.SourceMatrixIntertwinerCharpoly

/-! DUB-17/18 -> residual Frobenius association. Descend the actual field
characteristic polynomial along the injective coefficient embedding, then
reduce its literal integral matrix entrywise. No new lattice is chosen. -/
namespace Dubon2026
noncomputable section
open Matrix Polynomial
variable {R K k : Type*} [CommRing R] [Field K] [CommRing k]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem integral_matrix_charpoly_of_intertwiner
    (f : R →+* K) (hf : Function.Injective f)
    (A : Matrix n n R) (B : Matrix n n K)
    (e : (n → K) ≃ₗ[K] (n → K))
    (he : ∀ v, A.map f *ᵥ e v = e (B *ᵥ v))
    (P : R[X]) (hP : B.charpoly = P.map f) : A.charpoly = P := by
  apply Polynomial.map_injective f hf
  rw [← Matrix.charpoly_map, matrix_intertwiner_charpoly _ _ e he, hP]

theorem residue_matrix_charpoly_of_intertwiner
    (f : R →+* K) (hf : Function.Injective f) (r : R →+* k)
    (A : Matrix n n R) (B : Matrix n n K) (C : Matrix n n k)
    (e : (n → K) ≃ₗ[K] (n → K))
    (he : ∀ v, A.map f *ᵥ e v = e (B *ᵥ v))
    (hr : ∀ i j, C i j = r (A i j))
    (P : R[X]) (hP : B.charpoly = P.map f) :
    A.charpoly = P ∧ C.charpoly = P.map r := by
  have h := integral_matrix_charpoly_of_intertwiner f hf A B e he P hP
  refine ⟨h, ?_⟩
  have hc : C = A.map r := by ext i j; exact hr i j
  rw [hc, Matrix.charpoly_map, h]

theorem residue_matrix_one_of_intertwiner
    (f : R →+* K) (hf : Function.Injective f) (r : R →+* k)
    (A : Matrix n n R) (C : Matrix n n k)
    (e : (n → K) ≃ₗ[K] (n → K))
    (he : ∀ v, A.map f *ᵥ e v = e v)
    (hr : ∀ i j, C i j = r (A i j)) : A = 1 ∧ C = 1 := by
  have ha : A = 1 := by
    apply Matrix.map_injective hf
    change A.map f = (1 : Matrix n n R).map f
    rw [matrix_intertwiner_one _ e he, Matrix.map_one _ (map_zero f) (map_one f)]
  refine ⟨ha, ?_⟩
  have hc : C = A.map r := by ext i j; exact hr i j
  rw [hc, ha, Matrix.map_one _ (map_zero r) (map_one r)]

end
end Dubon2026
