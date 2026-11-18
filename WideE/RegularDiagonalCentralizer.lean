import WideE.LieMatrixCentralizer

/-! Persistence of the diagonal centralizer on the open where different
principal blocks have distinct eigenvalues. -/

noncomputable section

open scoped Ideal Matrix TensorProduct

namespace WideE

section Points

variable {k H Q A ι Λ : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing Q] [Algebra k Q] [CommRing A] [Algebra k A] [Fintype ι] [DecidableEq ι]

/-- The adjoint stabilizer of any algebra-valued tangent is its matrix
centralizer in a generating Hopf representation. -/
theorem hopfAdjoint_eq_self_iff_matrix_commutes
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (p : H →ₐ[k] A) (x : HopfLieVector k H A) :
    hopfAdjoint p x = x ↔ Commute (U.val.map p) (hopfCotangentMatrix U.val x) := by
  let M := hopfPointMatrix U hΔ hε p
  let N := hopfCotangentMatrix U.val x
  have hCov := hopfCotangentMatrix_adjoint U hΔ hε p x
  change hopfCotangentMatrix U.val (hopfAdjoint p x) = M.val * N * M.inv at hCov
  change hopfAdjoint p x = x ↔ Commute M.val N
  constructor
  · intro h
    rw [h] at hCov
    have hMul := congrArg (fun T : Matrix ι ι A => T * M.val) hCov
    change M.val * N = N * M.val
    simpa only [Matrix.mul_assoc, M.inv_val, Matrix.mul_one] using hMul.symm
  · intro h
    apply hopfCotangentMatrix_injective U.val hGen
    rw [hCov, h.eq, Matrix.mul_assoc, M.val_inv, Matrix.mul_one]

/-- Points through a diagonal quotient fix every diagonal tangent matrix. -/
theorem hopfAdjoint_eq_self_of_ker_le_of_diagonal
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (π : H →ₐ[k] Q) (hπ : ∀ i j, i ≠ j → π (U.val i j) = 0)
    (x : HopfLieVector k H A) (a : ι → A) (hx : hopfCotangentMatrix U.val x = Matrix.diagonal a)
    (p : H →ₐ[k] A) (hp : RingHom.ker π.toRingHom ≤ RingHom.ker p.toRingHom) :
    hopfAdjoint p x = x := by
  rw [hopfAdjoint_eq_self_iff_matrix_commutes U hΔ hε hGen, hx]
  change U.val.map p * Matrix.diagonal a = Matrix.diagonal a * U.val.map p
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  by_cases hij : i = j
  · subst j
    exact mul_comm _ _
  · have hZero : p (U.val i j) = 0 := hp (hπ i j hij)
    rw [hZero, zero_mul, mul_zero]

/-- Any diagonal tangent separating different principal blocks has the
same stabilizer functor as the diagonal quotient. The comparison is valid
in every coefficient algebra where the selected differences are units. -/
theorem hopfAdjoint_eq_self_iff_ker_le_of_separating_diagonal
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (w : ι → Λ) (π : H →ₐ[k] Q)
    (hπ : ∀ i j, i ≠ j → π (U.val i j) = 0)
    (hBlock : weightCentralizerIdeal w U.val = RingHom.ker π.toRingHom)
    (x : HopfLieVector k H A) (a : ι → A)
    (hX : hopfCotangentMatrix U.val x = Matrix.diagonal a)
    (hDistinct : ∀ i j, w i ≠ w j → IsUnit (a j - a i)) (p : H →ₐ[k] A) :
    hopfAdjoint p x = x ↔ RingHom.ker π.toRingHom ≤ RingHom.ker p.toRingHom := by
  constructor
  · intro h
    rw [hopfAdjoint_eq_self_iff_matrix_commutes U hΔ hε hGen, hX] at h
    rw [← hBlock]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, j, hij, rfl⟩
    change p (U.val i j) = 0
    have hEq := congrArg (fun N : Matrix ι ι A => N i j) h.eq
    change (U.val.map p * Matrix.diagonal a) i j = (Matrix.diagonal a * U.val.map p) i j at hEq
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, mul_comm (a i)] at hEq
    apply (hDistinct i j hij).mul_left_eq_zero.mp
    rw [mul_sub, hEq, sub_self]
  · exact hopfAdjoint_eq_self_of_ker_le_of_diagonal U hΔ hε hGen π hπ x a hX p

/-- A ground-field diagonal tangent retains this stabilizer condition
after extension to any coefficient algebra. -/
theorem hopfAdjoint_eq_self_iff_ker_le_of_separating_diagonal_scalar
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (w : ι → Λ) (π : H →ₐ[k] Q)
    (hπ : ∀ i j, i ≠ j → π (U.val i j) = 0)
    (hBlock : weightCentralizerIdeal w U.val = RingHom.ker π.toRingHom)
    (x : HopfLieVector k H k) (a : ι → k)
    (hX : hopfCotangentMatrix U.val x = Matrix.diagonal a)
    (hDistinct : ∀ i j, w i ≠ w j → a j ≠ a i) (p : H →ₐ[k] A) :
    hopfAdjoint p ((Algebra.ofId k A).toLinearMap.comp x) =
      (Algebra.ofId k A).toLinearMap.comp x ↔ RingHom.ker π.toRingHom ≤ RingHom.ker p.toRingHom := by
  apply hopfAdjoint_eq_self_iff_ker_le_of_separating_diagonal U hΔ hε hGen w π hπ hBlock _
    (algebraMap k A ∘ a) _ _ p
  · change (hopfCotangentMatrix U.val x).map (algebraMap k A) = _
    rw [hX]
    exact Matrix.diagonal_map (map_zero (algebraMap k A))
  · intro i l h
    rw [Function.comp_apply, Function.comp_apply, ← map_sub]
    exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hDistinct i l h))).map (algebraMap k A)

end Points

section Ideals

variable {k H Q ι Λ η : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing Q] [Algebra k Q] [Fintype ι] [DecidableEq ι] [Fintype η]

/-- The scheme-theoretic centralizer is constant on diagonal directions
separating the selected blocks. -/
theorem hopfAdjointCentralizerIdeal_eq_ker_of_separating_diagonal
    (b : Basis η k (HopfCotangent k H)) (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (w : ι → Λ) (π : H →ₐ[k] Q)
    (hπ : ∀ i j, i ≠ j → π (U.val i j) = 0)
    (hBlock : weightCentralizerIdeal w U.val = RingHom.ker π.toRingHom)
    (x : HopfLieVector k H k) (a : ι → k)
    (hX : hopfCotangentMatrix U.val x = Matrix.diagonal a)
    (hDistinct : ∀ i j, w i ≠ w j → a j ≠ a i) :
    hopfAdjointCentralizerIdeal b x = RingHom.ker π.toRingHom := by
  let I := hopfAdjointCentralizerIdeal b x
  let j := Ideal.Quotient.mkₐ k I
  change I = RingHom.ker π.toRingHom
  apply le_antisymm
  · let e := hopfAdjointCentralizerPoints (A := Q) b x
    let xQ := (Algebra.ofId k Q).toLinearMap.comp x
    let z : {p : H →ₐ[k] Q // hopfAdjoint p xQ = xQ} := ⟨π, (hopfAdjoint_eq_self_iff_ker_le_of_separating_diagonal_scalar
      U hΔ hε hGen w π hπ hBlock x a hX hDistinct π).mpr le_rfl⟩
    have hz : (e.symm z).comp j = π := congrArg Subtype.val (e.apply_symm_apply z)
    intro a ha
    change π a = 0
    rw [← hz, AlgHom.comp_apply, show j a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · have hFix :
        hopfAdjoint j ((Algebra.ofId k (H ⧸ I)).toLinearMap.comp x) =
          (Algebra.ofId k (H ⧸ I)).toLinearMap.comp x :=
      ((hopfAdjointCentralizerPoints (A := H ⧸ I) b x) (AlgHom.id k _)).prop
    rw [← show RingHom.ker j.toRingHom = I from Ideal.mk_ker]
    exact (hopfAdjoint_eq_self_iff_ker_le_of_separating_diagonal_scalar
      U hΔ hε hGen w π hπ hBlock x a hX hDistinct j).mp hFix

end Ideals

end WideE
