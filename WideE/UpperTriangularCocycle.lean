import WideE.ConnectedScalarKernels
import WideE.GaloisKernelReduction
import WideE.ScalarGaloisHilbert90

/-! Galois descent for connected groups with a generating upper triangular representation. -/

noncomputable section

open scoped TensorProduct BigOperators Matrix

namespace WideE

private theorem isHopfPointCoboundary_of_scalarGroup {k F E H : Type*}
    [CommRing k] [Field F] [Field E] [CommRing H] [HopfAlgebra k H]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (h : Function.Surjective (algebraMap k H)) (c : (E ≃ₐ[F] E) → H →ₐ[k] E) :
    IsHopfPointCoboundary c := by
  refine ⟨hopfPointOne, fun σ => AlgHom.ext fun x => ?_⟩
  obtain ⟨a, rfl⟩ := h x
  exact (AlgHom.commutes _ a).trans ((hopfPointOne : H →ₐ[k] E).commutes a).symm

section Triangular

local notation "K" => AlgebraicComplex

variable {F : Type*} [Field F] [Algebra K F]

attribute [local instance] additivePolynomialHopf

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 240000 in
private theorem upperTriangular_coboundary_of_count (d : ℕ) {H : Type}
    [CommRing H] [IsDomain H] [HopfAlgebra K H] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := K) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id)
    (hGen : Algebra.adjoin K (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤)
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (c : (E ≃ₐ[F] E) → H →ₐ[K] E) (hc : IsHopfPointCocycle c)
    (hCount : matrixNonidentityEntryCount M ≤ d) : IsHopfPointCoboundary c := by
  induction d using Nat.strong_induction_on generalizing H E with
  | h d ih =>
    classical
    by_cases hM : M = 1
    · exact isHopfPointCoboundary_of_scalarGroup
        (algebraMap_surjective_of_identity_generatingMatrix M hGen hM) c
    letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
    letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
    letI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
    letI : Algebra.FiniteType K H :=
      ⟨Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, hGen⟩⟩
    have hReduce {J : Type} [CommRing J] [IsDomain J] [HopfAlgebra K J]
        (π : H →ₐc[K] J) (hπ : Function.Surjective π) (i j : Fin n)
        (hne : M i j ≠ (1 : Matrix (Fin n) (Fin n) H) i j)
        (hkill : π (M i j) = (1 : Matrix (Fin n) (Fin n) J) i j)
        (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
        (a : (L ≃ₐ[F] L) → J →ₐ[K] L) (ha : IsHopfPointCocycle a) :
        IsHopfPointCoboundary a := by
      let f : H →ₐ[K] J := π
      let N := M.map f.toRingHom
      have hDecrease : matrixNonidentityEntryCount N < d :=
        (matrixNonidentityEntryCount_map_lt M f.toRingHom i j hne hkill).trans_le hCount
      obtain ⟨hΔ', hε', hUpper'⟩ := upperTriangularGroupMatrix_map M π hΔ hε hUpper
      exact ih _ hDecrease N hΔ' hε' hUpper' (generatingMatrix_map M f hπ hGen) L a ha le_rfl
    by_cases hDiag : ∀ i, M i i = 1
    · obtain ⟨i, j, hij, hx, hPrim⟩ := exists_upperTriangular_primitiveEntry M hΔ hUpper hDiag hM
      let x := M i j
      have hεx : Coalgebra.counit (R := K) x = 0 := (hε i j).trans (if_neg hij.ne)
      let I : Ideal H := Ideal.span {x}
      let hI : IsHopfIdeal K I := primitiveIdeal_isHopf x (by simpa only [add_comm] using hPrim) hεx
      let J := H ⧸ I
      letI : HopfAlgebra K J := hI.quotientHopf
      letI : IsDomain J := primitiveIdeal_quotient_isDomain x hx hεx hPrim
      let π := hI.quotientBialgHom
      have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
      let g := additiveScalarMap x hεx hPrim
      have hgX : g Polynomial.X = x := additiveScalarMap_X x hεx hPrim
      have hker : RingHom.ker (π : H →ₐ[K] J).toRingHom =
          (RingHom.ker (Bialgebra.counitAlgHom K (Polynomial K)).toRingHom).map
            (g : Polynomial K →ₐ[K] H).toRingHom := by
        rw [additivePolynomialHopf_ker_counit, Ideal.map_span, Set.image_singleton]
        change RingHom.ker (π : H →ₐ[K] J).toRingHom = Ideal.span {g Polynomial.X}
        rw [hgX]
        exact Ideal.mk_ker
      have hFlat := additiveGroupQuotient_faithfullyFlat g
        (additiveGroupQuotient_injective g (hgX.symm ▸ hx))
      have hQ := isHopfPointCoboundary_of_additivePolynomial (hc.precompose g)
      have hkill : π x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton x))
      apply isHopfPointCoboundary_of_quotient_and_kernel E g hFlat π hπ hker c hc hQ
      apply hReduce π hπ i j
      · rwa [Matrix.one_apply, if_neg hij.ne]
      · rw [Matrix.one_apply, if_neg hij.ne]
        exact hkill
    · obtain ⟨i, hi⟩ := not_forall.mp hDiag
      have hεi : Coalgebra.counit (R := K) (M i i) = 1 := (hε i i).trans (if_pos rfl)
      let x := upperTriangular_diagonalUnit M hΔ hUpper i hεi
      have hΔx := upperTriangular_diagonal_comul M hΔ hUpper i
      obtain ⟨r, u, _, hupow, hu, hεu, hΔu, hJu⟩ := exists_grouplikeRoot_domainKernel x hi hεi hΔx
      let I : Ideal H := Ideal.span {(u : H) - 1}
      let hI : IsHopfIdeal K I := grouplikeIdeal_isHopf (u : H) hΔu hεu
      let J := H ⧸ I
      letI : HopfAlgebra K J := hI.quotientHopf
      letI : IsDomain J := hJu
      let π := hI.quotientBialgHom
      have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
      let g := multiplicativeScalarMap u hεu hΔu
      have hgT : g (LaurentPolynomial.T 1) = u := multiplicativeScalarMap_T u hεu hΔu
      have hker : RingHom.ker (π : H →ₐ[K] J).toRingHom =
          (RingHom.ker (Bialgebra.counitAlgHom K (LaurentPolynomial K)).toRingHom).map
            (g : LaurentPolynomial K →ₐ[K] H).toRingHom := by
        rw [laurentPolynomial_ker_counit, Ideal.map_span, Set.image_singleton]
        change RingHom.ker (π : H →ₐ[K] J).toRingHom = Ideal.span {g (LaurentPolynomial.T 1 - 1)}
        rw [map_sub, map_one, hgT]
        exact Ideal.mk_ker
      have hFlat := multiplicativeGroupQuotient_faithfullyFlat g
        (multiplicativeGroupQuotient_injective g (hgT.symm ▸ hu))
      have hQ := isHopfPointCoboundary_of_laurentPolynomial (hc.precompose g)
      have hkillu : π (u : H) = 1 := by
        have hz : π ((u : H) - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_singleton ((u : H) - 1)))
        rwa [map_sub, map_one, sub_eq_zero] at hz
      have hkill : π (M i i) = 1 := by
        change π (x : H) = 1
        rw [← hupow, map_pow, hkillu, one_pow]
      apply isHopfPointCoboundary_of_quotient_and_kernel E g hFlat π hπ hker c hc hQ
      apply hReduce π hπ i i
      · simpa only [Matrix.one_apply, if_pos rfl] using hi
      · simpa only [Matrix.one_apply, if_pos rfl] using hkill

/-- A connected group over the algebraic numbers with a generating upper
triangular representation has trivial Galois cocycles over every base extension. -/
theorem upperTriangular_isHopfPointCoboundary {H : Type}
    [CommRing H] [IsDomain H] [HopfAlgebra K H] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := K) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id)
    (hGen : Algebra.adjoin K (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤)
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (c : (E ≃ₐ[F] E) → H →ₐ[K] E) (hc : IsHopfPointCocycle c) : IsHopfPointCoboundary c :=
  upperTriangular_coboundary_of_count (matrixNonidentityEntryCount M) M hΔ hε hUpper hGen E c hc le_rfl

/-- The cocycle theorem for a connected, reduced group in terms of its spectrum. -/
theorem upperTriangular_isHopfPointCoboundary_of_connected_reduced {H : Type}
    [CommRing H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] [HopfAlgebra K H] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := K) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id)
    (hGen : Algebra.adjoin K (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤)
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (c : (E ≃ₐ[F] E) → H →ₐ[K] E) (hc : IsHopfPointCocycle c) : IsHopfPointCoboundary c := by
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra.FiniteType K H := ⟨Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, hGen⟩⟩
  letI : IsDomain H := hopfDomain_of_connected_reduced (k := K) (H := H)
  exact upperTriangular_isHopfPointCoboundary M hΔ hε hUpper hGen E c hc

/-- A torsor over a field extension of the algebraic numbers under a connected
group with a generating upper triangular representation has a rational point. -/
theorem AffineHopfTorsor.nonempty_basePoint_of_upperTriangular {H S : Type}
    [CommRing H] [IsDomain H] [HopfAlgebra K H] [CommRing S]
    [Algebra K S] [Algebra F S] [IsScalarTower K F S] (T : AffineHopfTorsor K F S H) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := K) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id)
    (hGen : Algebra.adjoin K (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤) :
    Nonempty (S →ₐ[F] F) := by
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  apply T.nonempty_basePoint_of_finiteGalois_cocycle_triviality
  intro E _ _ c hc
  exact upperTriangular_isHopfPointCoboundary M hΔ hε hUpper hGen (FiniteGaloisIntermediateField.mk E) c hc

end Triangular

end WideE
