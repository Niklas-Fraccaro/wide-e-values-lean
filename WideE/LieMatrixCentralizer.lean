import WideE.HopfLieMatrixAdjoint
import WideE.WeightCentralizer
import WideE.AdjointToricDescent
import WideE.DenseExponentialProduct

/-! The universal adjoint centralizer of a diagonal Lie tangent is the
closed block centralizer in a faithful matrix realization. -/

noncomputable section

open scoped Ideal Matrix TensorProduct

namespace WideE

section Faithful

variable {k H A ι : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

/-- The tangent matrix is faithful over any coefficient algebra when the
original matrix coefficients generate the coordinate algebra. -/
theorem hopfCotangentMatrix_injective (U : Matrix ι ι H)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) = ⊤) :
    Function.Injective (hopfCotangentMatrix (k := k) (A := A) U) := by
  intro x y h
  let π := hopfCotangentProjection k H
  let E : Subalgebra k H := {
    carrier := {a | x (π a) = y (π a)}
    zero_mem' := by simp
    one_mem' := by
      change x (hopfCotangentProjection k H 1) = y (hopfCotangentProjection k H 1)
      rw [hopfCotangentProjection_one, map_zero, map_zero]
    add_mem' := fun {a b} ha hb => by
      change x (π a) = y (π a) at ha
      change x (π b) = y (π b) at hb
      change x (π (a + b)) = y (π (a + b))
      rw [map_add, map_add, map_add, ha, hb]
    mul_mem' := fun {a b} ha hb => by
      change x (hopfCotangentProjection k H a) = y (hopfCotangentProjection k H a) at ha
      change x (hopfCotangentProjection k H b) = y (hopfCotangentProjection k H b) at hb
      change x (hopfCotangentProjection k H (a * b)) = y (hopfCotangentProjection k H (a * b))
      simp only [hopfCotangentProjection_mul, map_add, map_smul, ha, hb]
    algebraMap_mem' := fun c => by
      change x (π (algebraMap k H c)) = y (π (algebraMap k H c))
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, π, hopfCotangentProjection_one, map_zero] }
  have hE : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) ≤ E := by
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact congrArg (fun M : Matrix ι ι A => M i j) h
  apply LinearMap.ext
  intro a
  obtain ⟨z, rfl⟩ := hopfCotangentProjection_surjective k H a
  apply hE
  rw [hGen]
  trivial

end Faithful

section CentralizerPoints

variable {k H A ι Λ : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A] [Fintype ι] [DecidableEq ι]

/-- Over any coefficient algebra, fixing a diagonal Lie tangent is the
same condition as preserving each of its matrix weight spaces. -/
theorem hopfAdjoint_eq_self_iff_weightBlocks
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (χ : ι → Λ) (d : Λ → k) (hDistinct : ∀ i j, χ i ≠ χ j → d (χ i) ≠ d (χ j))
    (x : HopfLieVector k H k)
    (hX : hopfCotangentMatrix U.val x = Matrix.diagonal (d ∘ χ))
    (p : H →ₐ[k] A) :
    hopfAdjoint p ((Algebra.ofId k A).toLinearMap.comp x) =
      (Algebra.ofId k A).toLinearMap.comp x ↔
      ∀ i j, χ i ≠ χ j → p (U.val i j) = 0 := by
  let M := hopfPointMatrix U hΔ hε p
  let y := (Algebra.ofId k A).toLinearMap.comp x
  let N := Matrix.diagonal (fun i => algebraMap k A (d (χ i)))
  have hY : hopfCotangentMatrix U.val y = N := by
    change (hopfCotangentMatrix U.val x).map (algebraMap k A) = _
    rw [hX]
    exact Matrix.diagonal_map (map_zero (algebraMap k A))
  have hAd := hopfCotangentMatrix_adjoint U hΔ hε p y
  change hopfCotangentMatrix U.val (hopfAdjoint p y) =
    M.val * hopfCotangentMatrix U.val y * M.inv at hAd
  rw [hY] at hAd
  change hopfAdjoint p y = y ↔ ∀ i j, χ i ≠ χ j → M.val i j = 0
  rw [← commute_weightDiagonal_iff χ d M.val hDistinct]
  constructor
  · intro h
    change M.val * N = N * M.val
    rw [h, hY] at hAd
    have hEq := congrArg (fun T : Matrix ι ι A => T * M.val) hAd
    simpa only [Matrix.mul_assoc, M.inv_val, Matrix.mul_one] using hEq.symm
  · intro h
    apply hopfCotangentMatrix_injective U.val hGen
    change Commute M.val N at h
    rw [hAd, hY, h.eq, Matrix.mul_assoc, M.val_inv, Matrix.mul_one]

end CentralizerPoints

section CentralizerIdeal

variable {k H ι Λ η : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι] [Fintype η]

/-- The weight-block equations and the adjoint equations define the same
scheme-theoretic centralizer of a diagonal tangent. -/
theorem hopfAdjointCentralizerIdeal_eq_weightBlocks
    (b : Basis η k (HopfCotangent k H)) (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (χ : ι → Λ) (d : Λ → k) (hDistinct : ∀ i j, χ i ≠ χ j → d (χ i) ≠ d (χ j))
    (x : HopfLieVector k H k)
    (hX : hopfCotangentMatrix U.val x = Matrix.diagonal (d ∘ χ)) :
    hopfAdjointCentralizerIdeal b x = weightCentralizerIdeal χ U.val := by
  let I := hopfAdjointCentralizerIdeal b x
  let J := weightCentralizerIdeal χ U.val
  let pI := Ideal.Quotient.mkₐ k I
  let pJ := Ideal.Quotient.mkₐ k J
  change I = J
  apply le_antisymm
  · have hJ : ∀ i j, χ i ≠ χ j → pJ (U.val i j) = 0 := fun i j h =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, j, h, rfl⟩)
    let e := hopfAdjointCentralizerPoints (A := H ⧸ J) b x
    let xJ := (Algebra.ofId k (H ⧸ J)).toLinearMap.comp x
    let z : {p : H →ₐ[k] (H ⧸ J) // hopfAdjoint p xJ = xJ} :=
      ⟨pJ, (hopfAdjoint_eq_self_iff_weightBlocks U hΔ hε hGen χ d hDistinct x hX pJ).mpr hJ⟩
    have hZ : (e.symm z).comp pI = pJ := congrArg Subtype.val (e.apply_symm_apply z)
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change pJ a = 0
    rw [← hZ, AlgHom.comp_apply, show pI a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · have hI :
        hopfAdjoint pI ((Algebra.ofId k (H ⧸ I)).toLinearMap.comp x) =
          (Algebra.ofId k (H ⧸ I)).toLinearMap.comp x :=
      ((hopfAdjointCentralizerPoints (A := H ⧸ I) b x) (AlgHom.id k (H ⧸ I))).prop
    have hB := (hopfAdjoint_eq_self_iff_weightBlocks U hΔ hε hGen χ d hDistinct x hX pI).mp hI
    apply Ideal.span_le.mpr
    rintro _ ⟨i, j, h, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hB i j h)

end CentralizerIdeal

section ExponentialCentralizer

variable {k H Q ι η β σ τ : Type*} [Field k] [CharZero k]
  [CommRing H] [HopfAlgebra k H] [IsDomain H] [Algebra.FiniteType k H]
  [CommRing Q] [HopfAlgebra k Q] [IsDomain Q]
  [Fintype ι] [DecidableEq ι] [Fintype η] [LinearOrder β] [Fintype σ] [Fintype τ]

local notation "𝔤" => HopfLieVector k H k
local notation "𝔱" => HopfLieVector k Q k

set_option maxHeartbeats 1800000 in
/-- The centralizer of the diagonal tangent is the actual torus quotient when
the torus directions and the strict triangular directions span the Lie algebra. -/
theorem hopfAdjointCentralizerIdeal_eq_ker_of_spanning_exponentials
    (b : Basis η k (HopfCotangent k H)) (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (w : ι → β) (d : β → k) (hDistinct : ∀ i j, w i ≠ w j → d (w i) ≠ d (w j))
    (x : 𝔤) (hX : hopfCotangentMatrix U.val x = Matrix.diagonal (d ∘ w))
    (π : H →ₐc[k] Q) (hπ : ∀ i j, w i ≠ w j → π (U.val i j) = 0)
    (xLower : σ → 𝔤) (xUpper : τ → 𝔤)
    (hLower : ∀ r i j, ¬w j < w i → hopfCotangentMatrix U.val (xLower r) i j = 0)
    (hUpper : ∀ r i j, ¬w i < w j → hopfCotangentMatrix U.val (xUpper r) i j = 0)
    (hSpan : Function.Surjective fun z : 𝔱 × ((σ ⊕ τ) → k) =>
      hopfLiePullback (π : H →ₐ[k] Q) (BialgHomClass.counitAlgHom_comp π) z.1 +
        ∑ j, z.2 j • Sum.elim xLower xUpper j) :
    hopfAdjointCentralizerIdeal b x = RingHom.ker (π : H →ₐ[k] Q).toRingHom := by
  have hB := hopfAdjointCentralizerIdeal_eq_weightBlocks b U hΔ hε hGen w d hDistinct x hX
  obtain ⟨f, Mlower, Mupper, hf, hl, hu, hProd⟩ := exists_dense_blockProduct_of_exponentials
    w U hΔ hε hGen π xLower xUpper hLower hUpper hSpan
  let A := Q ⊗[k] MvPolynomial (σ ⊕ τ) k
  let t : Q →ₐ[k] A := Algebra.TensorProduct.includeLeft
  have hQ : weightCentralizerIdeal w U.val = RingHom.ker (π : H →ₐ[k] Q).toRingHom :=
    weightCentralizerIdeal_eq_ker_of_dense_blockProduct (B := A) w U hGen
      (π : H →ₐ[k] Q) t f hf hπ Mlower Mupper hl.1 hl.2 hu.1 hu.2 hProd
  exact hB.trans hQ

end ExponentialCentralizer

end WideE
