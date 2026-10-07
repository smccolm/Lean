import Dubon2026.FiniteProjectedKernels

/-! # Exact finite products of commuting local compressions -/

namespace Dubon2026

section Monoid
variable {I M : Type*} [Monoid M]

/-- Local compressions commute when operators belonging to distinct indices commute. -/
theorem pairwise_compressed_operators (s : Finset I) (e a : I → M)
    (he : Set.Pairwise (↑s) (fun i j => Commute (e i) (e j)))
    (ha : Set.Pairwise (↑s) (fun i j => Commute (a i) (a j)))
    (hea : Set.Pairwise (↑s) (fun i j => Commute (e i) (a j))) :
    Set.Pairwise (↑s) (fun i j => Commute (e i * a i * e i) (e j * a j * e j)) := by
  have hAE : Set.Pairwise (↑s) (fun i j => Commute (a i) (e j)) :=
    fun _ hi _ hj hij => (hea hj hi hij.symm).symm
  exact Finset.noncommProd_mul_distrib_aux
    (Finset.noncommProd_mul_distrib_aux he ha hAE) he
      (fun _ hi _ hj hij => (he hi hj hij).mul_right (hea hi hj hij))

/-- The product of local compressions is exactly the common compression of the product.
No same-index commutation between e_i and a_i is required. -/
theorem noncommProd_compressions (s : Finset I) (e a : I → M)
    (he : Set.Pairwise (↑s) (fun i j => Commute (e i) (e j)))
    (ha : Set.Pairwise (↑s) (fun i j => Commute (a i) (a j)))
    (hea : Set.Pairwise (↑s) (fun i j => Commute (e i) (a j))) :
    s.noncommProd (fun i => e i * a i * e i) (pairwise_compressed_operators s e a he ha hea) =
      s.noncommProd e he * s.noncommProd a ha * s.noncommProd e he := by
  have hAE : Set.Pairwise (↑s) (fun i j => Commute (a i) (e j)) :=
    fun _ hi _ hj hij => (hea hj hi hij.symm).symm
  have hEA := Finset.noncommProd_mul_distrib_aux he ha hAE
  have hcross : Set.Pairwise (↑s) (fun i j => Commute (e i) ((e * a) j)) :=
    fun _ hi _ hj hij => (he hi hj hij).mul_right (hea hi hj hij)
  change s.noncommProd ((e * a) * e)
    (Finset.noncommProd_mul_distrib_aux hEA he hcross) = _
  rw [Finset.noncommProd_mul_distrib (e * a) e hEA he hcross,
    Finset.noncommProd_mul_distrib e a he ha hAE]

/-- A finite commuting product of actual idempotents is idempotent. -/
theorem noncommProd_idempotent (s : Finset I) (e : I → M)
    (he : Set.Pairwise (↑s) (fun i j => Commute (e i) (e j)))
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) : IsIdempotentElem (s.noncommProd e he) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsIdempotentElem.one
  | insert i s hi ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]
    apply IsIdempotentElem.mul_of_commute
    · exact s.noncommProd_commute _ _ _ (fun j hj =>
        he (Finset.mem_insert_self i s) (Finset.mem_insert_of_mem hj) (by aesop))
    · exact hid i (Finset.mem_insert_self i s)
    · exact ih _ (fun j hj => hid j (Finset.mem_insert_of_mem hj))

end Monoid
end Dubon2026
