import WideE.AffineGroupQuotient
import WideE.HopfSubalgebra
import WideE.UpperTriangularScalar

/-! The diagonal-block quotient and the unitriangular matrix of its actual kernel. -/

noncomputable section

open scoped BigOperators Matrix TensorProduct
open TensorProduct

namespace WideE

section DiagonalBlocks

universe u

variable {k H : Type u} {β : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  {n : ℕ} (b : Fin n → β) (M : Matrix (Fin n) (Fin n) H)

private def diagonalBlockEntries : Set H :=
  Set.range (fun ij : {ij : Fin n × Fin n // b ij.1 = b ij.2} => M ij.val.1 ij.val.2)

local notation "S" => hopfAntipodeAlgHom k H
local notation "Δ" => Bialgebra.comulAlgHom k H

/-- The coordinates of the diagonal blocks and their inverses generate this subalgebra. -/
def blockDiagonalAlgebra : Subalgebra k H :=
  Algebra.adjoin k (diagonalBlockEntries b M ∪ S '' diagonalBlockEntries b M)

local notation "Q" => blockDiagonalAlgebra (k := k) b M

theorem diagonalBlockEntry_mem {i j : Fin n} (hij : b i = b j) : M i j ∈ Q :=
  Algebra.subset_adjoin (Or.inl ⟨⟨(i, j), hij⟩, rfl⟩)

theorem blockDiagonalAlgebra_finiteType : Algebra.FiniteType k Q := by
  apply (Subalgebra.fg_iff_finiteType Q).mp
  apply Subalgebra.fg_def.mpr
  let E := diagonalBlockEntries b M
  have hE : E.Finite := Set.finite_range _
  exact ⟨E ∪ S '' E, hE.union (hE.image S), rfl⟩

private theorem blockDiagonalAlgebra_antipode : ∀ x : Q, S x.val ∈ Q := by
  have hLe : Q ≤ (Q).comap S := by
    apply Algebra.adjoin_le
    intro x hx
    change S x ∈ Q
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Algebra.subset_adjoin (Or.inr ⟨x, hx, rfl⟩)
    · have h := DFunLike.congr_fun (hopfAntipodeAlgHom_comp_self (k := k) (H := H)) y
      change S (S y) = y at h
      rw [h]
      exact Algebra.subset_adjoin (Or.inl hy)
  exact fun x => hLe x.property

variable [LinearOrder β]

private theorem diagonalBlockEntry_comul_mem
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hUpper : M.BlockTriangular b) {i j : Fin n} (hij : b i = b j) :
    Δ (M i j) ∈ (Algebra.TensorProduct.map (Q).val (Q).val).range := by
  change Coalgebra.comul (R := k) (M i j) ∈ _
  rw [hΔ]
  apply Subalgebra.sum_mem
  intro l _
  rcases lt_trichotomy (b l) (b i) with hlt | heq | hgt
  · rw [hUpper hlt, zero_tmul]
    exact Subalgebra.zero_mem _
  · let x : Q := ⟨M i l, diagonalBlockEntry_mem b M heq.symm⟩
    let y : Q := ⟨M l j, diagonalBlockEntry_mem b M (heq.trans hij)⟩
    exact ⟨x ⊗ₜ[k] y, rfl⟩
  · rw [hUpper (hij.symm.trans_lt hgt), tmul_zero]
    exact Subalgebra.zero_mem _

/-- Matrix comultiplication preserves the diagonal-block coordinate algebra. -/
theorem blockDiagonalAlgebra_isHopf
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (hUpper : M.BlockTriangular b) : IsHopfSubalgebra Q := by
  let j := (Q).val
  let f := Algebra.TensorProduct.map j j
  let s : Q →ₐ[k] Q := ((S).comp j).codRestrict Q (blockDiagonalAlgebra_antipode b M)
  have hs : j.comp s = (S).comp j := AlgHom.ext fun _ => rfl
  have hf : Q ≤ f.range.comap Δ := by
    apply Algebra.adjoin_le
    intro x hx
    change Δ x ∈ f.range
    rcases hx with ⟨⟨⟨i, j'⟩, hij⟩, rfl⟩ | ⟨y, ⟨⟨⟨i, j'⟩, hij⟩, rfl⟩, rfl⟩
    · exact diagonalBlockEntry_comul_mem b M hΔ hUpper hij
    · obtain ⟨z, hz⟩ := diagonalBlockEntry_comul_mem b M hΔ hUpper hij
      change f z = Δ (M i j') at hz
      refine ⟨Algebra.TensorProduct.comm k Q Q (Algebra.TensorProduct.map s s z), ?_⟩
      have hMap : f (Algebra.TensorProduct.map s s z) =
          Algebra.TensorProduct.map S S (f z) := by
        change (f.comp (Algebra.TensorProduct.map s s)) z =
          ((Algebra.TensorProduct.map S S).comp f) z
        simp only [f, ← Algebra.TensorProduct.map_comp, hs]
      change f (Algebra.TensorProduct.comm k Q Q (Algebra.TensorProduct.map s s z)) =
        ((Δ).comp S) (M i j')
      rw [← Algebra.TensorProduct.comm_comp_map_apply, hMap, hz, hopfComulAlgHom_comp_antipode]
      rfl
  exact ⟨fun x => hf x.property, blockDiagonalAlgebra_antipode b M⟩

variable
  (hΔ : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
  (hUpper : M.BlockTriangular b)

/-- Within the quotient algebra, the diagonal entries and their antipodes generate. -/
theorem blockDiagonalAlgebra_adjoin_self :
    letI := (blockDiagonalAlgebra_isHopf b M hΔ hUpper).hopfAlgebra
    let E : Set Q := Set.range fun ij : {ij : Fin n × Fin n // b ij.1 = b ij.2} =>
      (⟨M ij.val.1 ij.val.2, diagonalBlockEntry_mem b M ij.property⟩ : Q)
    Algebra.adjoin k (E ∪ hopfAntipodeAlgHom k Q '' E) = ⊤ := by
  let hQ := blockDiagonalAlgebra_isHopf b M hΔ hUpper
  letI := hQ.hopfAlgebra
  let f := (Q).val
  let E : Set Q := Set.range fun ij : {ij : Fin n × Fin n // b ij.1 = b ij.2} =>
    (⟨M ij.val.1 ij.val.2, diagonalBlockEntry_mem b M ij.property⟩ : Q)
  have hE : f '' E = diagonalBlockEntries b M := by
    change f '' Set.range _ = _
    rw [← Set.range_comp]
    rfl
  have hS : f '' (hopfAntipodeAlgHom k Q '' E) = hopfAntipodeAlgHom k H '' (f '' E) := by
    rw [Set.image_image, Set.image_image]
    exact congrArg (fun g : Q → H => g '' E) (funext hQ.antipode_apply)
  apply Subalgebra.map_injective (f := f) Subtype.val_injective
  change (Algebra.adjoin k (E ∪ hopfAntipodeAlgHom k Q '' E)).map f = (⊤ : Subalgebra k Q).map f
  rw [← Algebra.adjoin_image, Algebra.map_top, Set.image_union, hS, hE]
  exact (Subalgebra.range_val Q).symm

/-- The coordinate map of the diagonal-block group quotient. -/
def blockDiagonalQuotientMap :
    letI := (blockDiagonalAlgebra_isHopf b M hΔ hUpper).hopfAlgebra
    Q →ₐc[k] H :=
  (blockDiagonalAlgebra_isHopf b M hΔ hUpper).bialgHom

/-- The actual map to the diagonal-block group is faithfully flat. -/
theorem blockDiagonalQuotient_faithfullyFlat [IsAlgClosed k] [IsDomain H] [Algebra.FiniteType k H] :
    letI := (blockDiagonalAlgebra_isHopf b M hΔ hUpper).hopfAlgebra
    let j : Q →ₐ[k] H := blockDiagonalQuotientMap b M hΔ hUpper
    letI : Algebra Q H := j.toRingHom.toAlgebra
    Module.FaithfullyFlat Q H := by
  letI := (blockDiagonalAlgebra_isHopf b M hΔ hUpper).hopfAlgebra
  letI : Algebra.FiniteType k Q := blockDiagonalAlgebra_finiteType b M
  exact affineGroupQuotient_faithfullyFlat (k := k) (H := H)
    (blockDiagonalQuotientMap b M hΔ hUpper) Subtype.val_injective

/-- The closed kernel is cut out by the augmentation ideal of the diagonal blocks. -/
def blockDiagonalKernelIdeal : Ideal H :=
  letI := (blockDiagonalAlgebra_isHopf b M hΔ hUpper).hopfAlgebra
  hopfKernelIdeal (blockDiagonalQuotientMap b M hΔ hUpper)

theorem blockDiagonalKernelIdeal_isHopf : IsHopfIdeal k (blockDiagonalKernelIdeal b M hΔ hUpper) := by
  letI := (blockDiagonalAlgebra_isHopf b M hΔ hUpper).hopfAlgebra
  exact hopfKernelIdeal_isHopf (blockDiagonalQuotientMap b M hΔ hUpper)

local notation "I" => blockDiagonalKernelIdeal b M hΔ hUpper

/-- The given matrix with coefficients in the coordinate ring of the actual kernel. -/
def blockDiagonalKernelMatrix : Matrix (Fin n) (Fin n) (H ⧸ I) :=
  M.map (Ideal.Quotient.mk I)

/-- In the actual kernel, each diagonal block is the identity matrix. -/
theorem blockDiagonalKernelMatrix_on_block
    (hε : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    {i j : Fin n} (hij : b i = b j) :
    blockDiagonalKernelMatrix b M hΔ hUpper i j = if i = j then 1 else 0 := by
  let hQ := blockDiagonalAlgebra_isHopf b M hΔ hUpper
  letI := hQ.hopfAlgebra
  let f : Q →ₐ[k] H := blockDiagonalQuotientMap b M hΔ hUpper
  let e := Bialgebra.counitAlgHom k Q
  let x : Q := ⟨M i j, diagonalBlockEntry_mem b M hij⟩
  have he : e x = if i = j then 1 else 0 := (hQ.counit_apply x).trans (hε i j)
  have hx : x - algebraMap k Q (e x) ∈ RingHom.ker e.toRingHom := by
    change e (x - algebraMap k Q (e x)) = 0
    simp
  have hI : f (x - algebraMap k Q (e x)) ∈ I := Ideal.mem_map_of_mem f.toRingHom hx
  let p := Ideal.Quotient.mkₐ k I
  have hz : p (f (x - algebraMap k Q (e x))) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hI
  rw [map_sub, f.commutes, map_sub, p.commutes, he, sub_eq_zero] at hz
  simpa only [apply_ite (algebraMap k (H ⧸ I)), map_one, map_zero] using hz

/-- Ordered diagonal blocks give a unitriangular representation of the kernel. -/
theorem blockDiagonalKernelMatrix_unitriangular (hb : Monotone b)
    (hε : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0) :
    (blockDiagonalKernelMatrix b M hΔ hUpper).BlockTriangular id ∧
      ∀ i, blockDiagonalKernelMatrix b M hΔ hUpper i i = 1 := by
  refine ⟨?_, fun i => (blockDiagonalKernelMatrix_on_block b M hΔ hUpper hε
    (i := i) (j := i) rfl).trans (if_pos rfl)⟩
  intro i j hij
  change j < i at hij
  rcases (hb hij.le).lt_or_eq with hlt | heq
  · change Ideal.Quotient.mk I (M i j) = 0
    rw [hUpper hlt, map_zero]
  · exact (blockDiagonalKernelMatrix_on_block b M hΔ hUpper hε heq.symm).trans (if_neg hij.ne')

/-- The kernel matrix keeps the Hopf relations and generation of the original matrix. -/
theorem blockDiagonalKernelMatrix_relations
    (hε : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤) :
    letI := (blockDiagonalKernelIdeal_isHopf b M hΔ hUpper).quotientHopf
    let N := blockDiagonalKernelMatrix b M hΔ hUpper
    (∀ i j, Coalgebra.comul (R := k) (N i j) = ∑ l, N i l ⊗ₜ[k] N l j) ∧
      (∀ i j, Coalgebra.counit (R := k) (N i j) = if i = j then 1 else 0) ∧
      Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => N ij.1 ij.2) = ⊤ := by
  let hI := blockDiagonalKernelIdeal_isHopf b M hΔ hUpper
  letI := hI.quotientHopf
  let π := hI.quotientBialgHom
  obtain ⟨hD, he⟩ := hopfMatrixRelations_map M π hΔ hε
  exact ⟨hD, he, generatingMatrix_map M (π : H →ₐ[k] H ⧸ I) (Ideal.Quotient.mkₐ_surjective k I) hGen⟩

end DiagonalBlocks

end WideE
