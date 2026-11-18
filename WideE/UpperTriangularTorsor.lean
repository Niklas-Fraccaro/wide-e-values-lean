import WideE.ConnectedScalarKernels
import WideE.GenericComponentSection

/-! Sections for torsors under a group with a generating upper triangular representation. -/

noncomputable section

open scoped TensorProduct BigOperators Matrix

namespace WideE

private theorem section_of_scalarGroup {K B S H : Type*} [CommRing K] [CommRing B]
    [CommRing S] [CommRing H] [Algebra K B] [Algebra K S] [Algebra B S] [IsScalarTower K B S]
    [HopfAlgebra K H] (T : AffineHopfTorsor K B S H)
    (h : Function.Surjective (algebraMap K H)) : Nonempty (S →ₐ[B] B) := by
  have heval (z : S ⊗[K] H) : z = (coactionCounit z) ⊗ₜ[K] (1 : H) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv =>
      rw [map_add, TensorProduct.add_tmul]
      exact congrArg₂ (· + ·) hu hv
    | tmul s a =>
      obtain ⟨c, rfl⟩ := h a
      have hc : Bialgebra.counitAlgHom K H (algebraMap K H c) = c := by simp
      change s ⊗ₜ[K] algebraMap K H c =
        (s * algebraMap K S (Bialgebra.counitAlgHom K H (algebraMap K H c))) ⊗ₜ[K] (1 : H)
      rw [hc, mul_comm s, ← Algebra.smul_def, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
  have hρ (s : S) : T.coaction s = s ⊗ₜ[K] (1 : H) := by
    simpa only [T.counital] using heval (T.coaction s)
  letI := T.faithfullyFlat
  have hinj : Function.Injective (algebraMap B S) := by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    simpa only [Ideal.map_bot, ← RingHom.ker_eq_comap_bot] using
      Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (⊥ : Ideal B)
  let f := Algebra.linearMap B S
  let p := (LinearMap.range f).mkQ
  have hp1 : p (1 : S) = 0 :=
    Submodule.Quotient.mk_eq_zero _ |>.mpr ⟨1, map_one (algebraMap B S)⟩
  have hsurj (s : S) : ∃ b : B, algebraMap B S b = s := by
    have heq : (1 : S) ⊗ₜ[B] s = s ⊗ₜ[B] (1 : S) := by
      apply T.chart.symm.injective
      rw [T.chart_symm_apply, T.chart_symm_apply, hρ s, map_one, mul_one,
        ← Algebra.TensorProduct.one_def, one_mul]
    have hz : p s = 0 := by
      apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := B) (B := S)
        (S ⧸ LinearMap.range f)
      rw [map_zero]
      change (1 : S) ⊗ₜ[B] p s = 0
      simpa only [LinearMap.lTensor_tmul, hp1, TensorProduct.tmul_zero] using
        congrArg (p.lTensor S) heq
    exact Submodule.Quotient.mk_eq_zero (LinearMap.range f) |>.mp hz
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId B S) ⟨hinj, hsurj⟩).symm.toAlgHom⟩

section IntegralGroup

local notation "K" => AlgebraicComplex

variable {B : Type} [CommRing B] [Algebra K B] [IsDomain B] [IsPrincipalIdealRing B]

attribute [local instance] additivePolynomialHopf

omit [IsDomain B] [IsPrincipalIdealRing B] in
private theorem section_of_actualScalarKernel {S A J : Type} [CommRing S] [CommRing A] [CommRing J]
    [Algebra K S] [Algebra K A] [Algebra B S] [IsScalarTower K B S] [HopfAlgebra K J]
    (γ : A →ₐ[K] S) (ev : A →ₐ[K] K)
    (U : let Q := B ⊗[K] A
      let f := kernelScalarBaseMap (B := B) γ
      letI : Algebra Q S := f.toRingHom.toAlgebra
      letI : IsScalarTower K Q S := IsScalarTower.of_algHom (f.restrictScalars K)
      AffineHopfTorsor K Q S J)
    (hJ : ∀ (S' : Type) [CommRing S'] [Algebra K S'] [Algebra B S'] [IsScalarTower K B S'],
      AffineHopfTorsor K B S' J → Nonempty (S' →ₐ[B] B)) : Nonempty (S →ₐ[B] B) := by
  let Q := B ⊗[K] A
  let f := kernelScalarBaseMap (B := B) γ
  letI : Algebra Q S := f.toRingHom.toAlgebra
  letI : IsScalarTower K Q S := IsScalarTower.of_algHom (f.restrictScalars K)
  letI : IsScalarTower B Q S := IsScalarTower.of_algHom f
  let σ : Q →ₐ[B] B := Algebra.TensorProduct.lift (AlgHom.id B B)
    ((Algebra.ofId K B).comp ev) (fun _ _ => Commute.all _ _)
  letI : Algebra Q B := σ.toRingHom.toAlgebra
  letI : IsScalarTower K Q B := IsScalarTower.of_algHom (σ.restrictScalars K)
  letI : SMulCommClass Q K B := ⟨fun a c b => by
    simp only [Algebra.smul_def]
    rw [← mul_assoc, ← mul_assoc, mul_comm (algebraMap Q B a)]⟩
  let S' := B ⊗[Q] S
  letI : Algebra K S' := Algebra.TensorProduct.leftAlgebra
  letI : Algebra B S' := Algebra.TensorProduct.leftAlgebra
  letI : IsScalarTower K B S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨τ⟩ := hJ S' (U.overSection σ)
  exact ⟨sectionFromPullback σ τ⟩

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 240000 in
private theorem upperTriangular_section_of_count (d : ℕ) {S H : Type} [CommRing S] [CommRing H]
    [IsDomain H] [HopfAlgebra K H] [Algebra K S] [Algebra B S] [IsScalarTower K B S]
    (T : AffineHopfTorsor K B S H) {n : ℕ} (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := K) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id)
    (hGen : Algebra.adjoin K (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤)
    (hCount : matrixNonidentityEntryCount M ≤ d) : Nonempty (S →ₐ[B] B) := by
  induction d using Nat.strong_induction_on generalizing S H with
  | h d ih =>
    classical
    by_cases hM : M = 1
    · exact section_of_scalarGroup T (algebraMap_surjective_of_identity_generatingMatrix M hGen hM)
    letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
    letI : Algebra.FiniteType K H := T.group_finiteType
    have hReduce {J : Type} [CommRing J] [IsDomain J] [HopfAlgebra K J]
        (π : H →ₐc[K] J) (hπ : Function.Surjective π) (i j : Fin n)
        (hne : M i j ≠ (1 : Matrix (Fin n) (Fin n) H) i j)
        (hkill : π (M i j) = (1 : Matrix (Fin n) (Fin n) J) i j) :
        ∀ (S' : Type) [CommRing S'] [Algebra K S'] [Algebra B S'] [IsScalarTower K B S'],
          AffineHopfTorsor K B S' J → Nonempty (S' →ₐ[B] B) := by
      intro S' _ _ _ _ U
      let f : H →ₐ[K] J := π
      let N := M.map f.toRingHom
      have hDecrease : matrixNonidentityEntryCount N < d :=
        (matrixNonidentityEntryCount_map_lt M f.toRingHom i j hne hkill).trans_le hCount
      obtain ⟨hΔ', hε', hUpper'⟩ := upperTriangularGroupMatrix_map M π hΔ hε hUpper
      exact ih _ hDecrease U N hΔ' hε' hUpper' (generatingMatrix_map M f hπ hGen) le_rfl
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
      have hker : RingHom.ker (π : H →ₐ[K] J).toRingHom = Ideal.span {g Polynomial.X} := by
        rw [hgX]
        exact Ideal.mk_ker
      have hFlat := additiveGroupQuotient_faithfullyFlat g
        (additiveGroupQuotient_injective g (hgX.symm ▸ hx))
      obtain ⟨s, _, ⟨U, _⟩⟩ := T.exists_additiveKernelTorsor g hFlat π hπ hker
      have hkill : π x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton x))
      apply section_of_actualScalarKernel (Polynomial.aeval s) (Polynomial.aeval (0 : K)) U
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
      have hker : RingHom.ker (π : H →ₐ[K] J).toRingHom = Ideal.span {g (LaurentPolynomial.T 1) - 1} := by
        rw [hgT]
        exact Ideal.mk_ker
      have hFlat := multiplicativeGroupQuotient_faithfullyFlat g
        (multiplicativeGroupQuotient_injective g (hgT.symm ▸ hu))
      obtain ⟨v, _, ⟨U, _⟩⟩ := T.exists_multiplicativeKernelTorsor g hFlat π hπ hker
      have hkillu : π (u : H) = 1 := by
        have hz : π ((u : H) - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_singleton ((u : H) - 1)))
        rwa [map_sub, map_one, sub_eq_zero] at hz
      have hkill : π (M i i) = 1 := by
        change π (x : H) = 1
        rw [← hupow, map_pow, hkillu, one_pow]
      let ev : LaurentPolynomial K →ₐ[K] K := { evalAtOne K with commutes' := evalAtOne_C K }
      apply section_of_actualScalarKernel (laurentKernelCoordinate v) ev U
      apply hReduce π hπ i i
      · simpa only [Matrix.one_apply, if_pos rfl] using hi
      · simpa only [Matrix.one_apply, if_pos rfl] using hkill

/-- A torsor over a principal domain under an integral group with a generating
upper triangular representation has a section. -/
theorem upperTriangular_affineHopfTorsor_has_section_of_pid {S H : Type} [CommRing S] [CommRing H]
    [IsDomain H] [HopfAlgebra K H] [Algebra K S] [Algebra B S] [IsScalarTower K B S]
    (T : AffineHopfTorsor K B S H) {n : ℕ} (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := K) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id)
    (hGen : Algebra.adjoin K (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤) :
    Nonempty (S →ₐ[B] B) :=
  upperTriangular_section_of_count (matrixNonidentityEntryCount M) T M hΔ hε hUpper hGen le_rfl

end IntegralGroup

section LaurentBase

local notation "K" => AlgebraicComplex
local notation "Rₗ" => LaurentPolynomial K

variable {S H : Type} [CommRing S] [CommRing H] [HopfAlgebra K H]
  [Algebra K S] [Algebra Rₗ S] [IsScalarTower K Rₗ S]

/-- A Laurent-line torsor under an integral affine group with a generating
upper triangular representation has a section. -/
theorem upperTriangular_affineHopfTorsor_has_section [IsDomain H]
    (T : AffineHopfTorsor K Rₗ S H) {n : ℕ} (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := K) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id)
    (hGen : Algebra.adjoin K (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤) :
    Nonempty (S →ₐ[Rₗ] Rₗ) := by
  letI : IsPrincipalIdealRing Rₗ := StrictEUnit.laurentPolynomial_isPrincipalIdealRing K
  exact upperTriangular_affineHopfTorsor_has_section_of_pid T M hΔ hε hUpper hGen

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- A generic point removes the finite component obstruction for a reduced
upper triangular Laurent-line torsor. -/
theorem upperTriangular_affineHopfTorsor_has_section_of_genericPoint [IsReduced H]
    {F : Type} [CommRing F] [Algebra Rₗ F] [IsFractionRing Rₗ F]
    (T : AffineHopfTorsor K Rₗ S H) (p : S →ₐ[Rₗ] F) {n : ℕ} (M : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j, Coalgebra.comul (R := K) (M i j) = ∑ l, M i l ⊗ₜ[K] M l j)
    (hε : ∀ i j, Coalgebra.counit (R := K) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular id)
    (hGen : Algebra.adjoin K (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤) :
    Nonempty (S →ₐ[Rₗ] Rₗ) := by
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  letI : IsPrincipalIdealRing Rₗ := StrictEUnit.laurentPolynomial_isPrincipalIdealRing K
  letI : Algebra.FiniteType K H := T.group_finiteType
  obtain ⟨G⟩ := nonempty_componentHopfPresentation (hopfAntipodeAlgHom K H)
    (hopfAntipodeAlgHom_toLinearMap (k := K) (H := H))
  let J := G.IdentityComponent
  letI : HopfAlgebra K J := G.identityHopf
  letI : IsDomain J := G.identityComponent_isDomain
  let π : H →ₐc[K] J := BialgHom.ofAlgHom G.identityQuotient
    (LinearMap.ext fun a => AlgHom.congr_fun G.identityCounit_comp_quotient a)
    (LinearMap.ext fun a => (G.identityComul_quotient a).symm)
  let g : H →ₐ[K] J := π
  let N := M.map g.toRingHom
  obtain ⟨hΔ', hε', hUpper'⟩ := upperTriangularGroupMatrix_map M π hΔ hε hUpper
  have hGen' := generatingMatrix_map M g G.identityQuotient_surjective hGen
  refine nonempty_section_of_identityComponent_generic_sections T G p ?_
  intro A _ _ _ _ U _
  exact upperTriangular_affineHopfTorsor_has_section U N hΔ' hε' hUpper' hGen'

end LaurentBase

end WideE
