import WideE.HopfLieMatrixAdjoint
import WideE.BlockExponential

/-! A polynomial-valued exponential point has the actual prescribed Lie
tangent at its identity specialization. -/

noncomputable section

open StrictEUnit
open scoped Polynomial Matrix TensorProduct

namespace WideE

variable {k H ι β : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

local notation "ε" => Bialgebra.counitAlgHom k H

/-- The derivation on a polynomial exponential curve intertwines the
invariant derivation on the coordinate algebra. -/
theorem polynomialExponential_intertwines_derivation
    (U : Matrix ι ι H)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U ij.1 ij.2) = ⊤)
    (D : Derivation k H H) (N : Matrix ι ι k) (hN : IsNilpotent N)
    (hD : matrixDerivative D U = U * (algebraMap k H).mapMatrix N)
    (q : H →ₐ[k] k[X]) (hq : U.map q = polynomialMatrixExponential N) (a : H) :
    Polynomial.derivative (q a) = q (D a) := by
  letI : Algebra H k[X] := q.toRingHom.toAlgebra
  letI : IsScalarTower k H k[X] := IsScalarTower.of_algHom q
  let E := (Polynomial.derivative' (R := k)).compAlgebraMap H
  let F := (Algebra.linearMap H k[X]).compDer D
  have hEF : E = F := by
    apply Derivation.ext_of_adjoin_eq_top _ hGen
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change Polynomial.derivative (q (U i j)) = q (D (U i j))
    have h0 : matrixDerivative (Polynomial.derivative' (R := k)) (U.map q) =
        (U.map q) * (algebraMap k k[X]).mapMatrix N :=
      hq.symm ▸ polynomialMatrixExponential_derivative N hN
    have h1 : (matrixDerivative D U).map q =
        (U.map q) * (algebraMap k k[X]).mapMatrix N := by
      rw [hD]
      change q.toRingHom.mapMatrix (U * (algebraMap k H).mapMatrix N) = _
      rw [map_mul]
      congr 1
      exact Matrix.ext fun i j => q.commutes (N i j)
    exact congrArg (fun M : Matrix ι ι k[X] => M i j) (h0.trans h1.symm)
  exact DFunLike.congr_fun hEF a

/-- A strictly block upper triangular Lie tangent integrates to a
polynomial-valued group point whose differential is the original tangent. -/
theorem exists_hopfPolynomialPoint_of_strictBlocks [LinearOrder β]
    (w : ι → β) (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (x : HopfLieVector k H k)
    (hX : ∀ i j, ¬w i < w j → hopfCotangentMatrix U.val x i j = 0) :
    ∃ q : H →ₐ[k] k[X],
      BlockUnitriangular w (U.val.map q) ∧
      (Polynomial.aeval (0 : k)).comp q = ε ∧
      ∀ a, Polynomial.aeval (0 : k) (Polynomial.derivative (q a)) =
        x (hopfCotangentProjection k H a) := by
  let d := hopfLieVectorInvariantDerivations x
  let N := hopfCotangentMatrix U.val x
  have hDt : matrixDerivative d.val U.val = U.val * (algebraMap k H).mapMatrix N := by
    apply Matrix.ext
    intro i j
    change d.val (U.val i j) = ∑ l, U.val i l * algebraMap k H (N l j)
    have hNmat : N = hopfLieMatrix U.val d := (hopfLieMatrix_invariantDerivations U.val x).symm
    rw [hNmat]
    exact hopfInvariantDerivation_matrixCoefficient U.val hΔ d i j
  have hOne : U.val.map (ε) = (1 : Matrix ι ι k) := Matrix.ext fun i j =>
    (hε i j).trans (Matrix.one_apply (i := i) (j := j)).symm
  have hN : IsNilpotent N := isNilpotent_of_strictBlockTriangular w N hX
  obtain ⟨q, hq, hq0⟩ := exists_hopfPolynomialPoint_matrixExponential U.val hGen hOne d.val N hN hDt
  refine ⟨q, hq.symm ▸ polynomialMatrixExponential_blockUnitriangular w N hX, hq0, fun a => ?_⟩
  rw [polynomialExponential_intertwines_derivation U.val hGen d.val N hN hDt q hq]
  change ((Polynomial.aeval (0 : k)).comp q) (d.val a) = _
  rw [hq0, hopfLieVectorInvariantDerivations_counit]

end WideE
