import GafniTao.WooleyResidueRefinement
#check Finset.sum_fiberwise
#check Finset.sum_bij
#check Finset.sum_bij'
#check Finset.filter_product
#check Finset.product_filter
#check Finset.sum_product
#check Finset.sum_product_left
#check Finset.sum_product_right
#check Fin.sum_univ_succ
#check Fin.prod_univ_succ
#check Fintype.sum_fin_eq_sum_range
#check Finset.sum_subtype
#check Finset.sum_attach
#check Finset.sum_subtype_of_mem
example {ι : Type*} (t : Finset ι) : Fintype {i : ι // i ∈ t} := inferInstance
#check Fintype.ofFinset
#check Finset.fintypeCoeSort
