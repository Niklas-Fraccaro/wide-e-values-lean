import WideE.HopfLieMatrixAdjoint
import WideE.HopfMatrixExponential
import WideE.AdjointExponential

/-! A nilpotent Lie correction is realized by an actual affine group point. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

variable {k H ι : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
variable [Fintype ι] [DecidableEq ι]

local notation "𝔤" => hopfInvariantDerivations k H

omit [CharZero k] in
private theorem leftAdjoint_pow_map (ρ : 𝔤 →ₗ⁅k⁆ Matrix ι ι k) (x y : 𝔤) (n : ℕ) :
    ρ (((leftAdjointDerivation k x).toLinearMap ^ n) y) =
      ((leftAdjointDerivation k (ρ x)).toLinearMap ^ n) (ρ y) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    change ρ (leftAdjointDerivation k x (((leftAdjointDerivation k x).toLinearMap ^ n) y)) =
      leftAdjointDerivation k (ρ x) (((leftAdjointDerivation k (ρ x)).toLinearMap ^ n) (ρ y))
    rw [leftAdjointDerivation_apply, leftAdjointDerivation_apply, LieHom.map_lie, ih]

/-- The adjoint exponential of a tangent with nilpotent matrix is the adjoint action
of a point of the original Hopf group with the prescribed exponential matrix. -/
theorem exists_hopfPoint_lieAdjointExp_with_matrix (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (D : 𝔤) (hN : IsNilpotent (hopfLieMatrix U.val D)) :
    letI : LieAlgebra ℚ 𝔤 := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ k 𝔤))
    ∃ (h : IsNilpotent (leftAdjointDerivation k D).toLinearMap) (p : H →ₐ[k] k),
      (hopfPointMatrix U hD he p).val = IsNilpotent.exp (hopfLieMatrix U.val D) ∧
      ∀ y : HopfLieVector k H k,
        hopfLieVectorInvariantDerivations (hopfAdjoint p y) =
          LieDerivation.exp (leftAdjointDerivation k D) h (hopfLieVectorInvariantDerivations y) := by
  letI : LieAlgebra ℚ 𝔤 := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ k 𝔤))
  let ρ := hopfLieMatrixHom U.val hD
  let N := hopfLieMatrix U.val D
  have hOne : U.val.map (Bialgebra.counitAlgHom k H) = 1 := by
    apply Matrix.ext
    intro i j
    change Coalgebra.counit (R := k) (U.val i j) = (1 : Matrix ι ι k) i j
    rw [he, Matrix.one_apply]
  have hDer : StrictEUnit.matrixDerivative D.val U.val = U.val * (algebraMap k H).mapMatrix N := by
    apply Matrix.ext
    intro i j
    exact hopfInvariantDerivation_matrixCoefficient U.val hD D i j
  obtain ⟨p, hP⟩ := exists_hopfPoint_matrixExponential U.val hGen hOne D.val N hN hDer 1
  rw [one_smul] at hP
  have hI : Function.Injective ρ := hopfLieMatrixHom_injective U.val hD hGen
  let hMat := isNilpotent_leftAdjointDerivation_of_isNilpotent (k := k) N hN
  have hLie : IsNilpotent (leftAdjointDerivation k D).toLinearMap := by
    obtain ⟨n, hn⟩ := hMat
    refine ⟨n, LinearMap.ext fun y => hI ?_⟩
    change ρ (((leftAdjointDerivation k D).toLinearMap ^ n) y) = ρ 0
    rw [leftAdjoint_pow_map, show (leftAdjointDerivation k (ρ D)).toLinearMap ^ n = 0 from hn,
      LinearMap.zero_apply, LieHom.map_zero]
  refine ⟨hLie, p, hP, fun y => hI ?_⟩
  have hAd := hopfCotangentMatrix_adjoint U hD he p y
  have hExp := map_leftAdjointExp ρ D (hopfLieVectorInvariantDerivations y) hLie hMat
  change ρ (LieDerivation.exp (leftAdjointDerivation k D) hLie (hopfLieVectorInvariantDerivations y)) =
    LieDerivation.exp (leftAdjointDerivation k N) hMat (ρ (hopfLieVectorInvariantDerivations y)) at hExp
  rw [leftAdjointExp_eq_exponential_conjugation (k := k) N hN] at hExp
  let M := hopfPointMatrix U hD he p
  have hM : M.val = IsNilpotent.exp N := hP
  have hInv : M.inv = IsNilpotent.exp (-N) := by
    calc
      M.inv = M.inv * (M.val * IsNilpotent.exp (-N)) := by rw [hM, hN.exp_mul_exp_neg_self, mul_one]
      _ = IsNilpotent.exp (-N) := by rw [← mul_assoc, M.inv_val, one_mul]
  change hopfLieMatrix U.val (hopfLieVectorInvariantDerivations (hopfAdjoint p y)) =
    ρ (LieDerivation.exp (leftAdjointDerivation k D) hLie (hopfLieVectorInvariantDerivations y))
  rw [hopfLieMatrix_invariantDerivations, hExp]
  change hopfCotangentMatrix U.val (hopfAdjoint p y) =
    IsNilpotent.exp N * hopfLieMatrix U.val (hopfLieVectorInvariantDerivations y) * IsNilpotent.exp (-N)
  rw [hopfLieMatrix_invariantDerivations]
  change hopfCotangentMatrix U.val (hopfAdjoint p y) = M.val * hopfCotangentMatrix U.val y * M.inv at hAd
  rw [hM, hInv] at hAd
  exact hAd

/-- The adjoint exponential of a tangent with nilpotent matrix is the adjoint action
of a point of the original Hopf group. -/
theorem exists_hopfPoint_lieAdjointExp (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (D : 𝔤) (hN : IsNilpotent (hopfLieMatrix U.val D)) :
    letI : LieAlgebra ℚ 𝔤 := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ k 𝔤))
    ∃ (h : IsNilpotent (leftAdjointDerivation k D).toLinearMap) (p : H →ₐ[k] k),
      ∀ y : HopfLieVector k H k,
        hopfLieVectorInvariantDerivations (hopfAdjoint p y) =
          LieDerivation.exp (leftAdjointDerivation k D) h (hopfLieVectorInvariantDerivations y) := by
  obtain ⟨h, p, _, hp⟩ := exists_hopfPoint_lieAdjointExp_with_matrix U hD he hGen D hN
  exact ⟨h, p, hp⟩

end WideE
