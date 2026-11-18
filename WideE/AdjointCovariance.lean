import WideE.AdjointRegularLocus

/-! Conjugation invariance of the characteristic polynomial of the actual orbit derivative. -/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

section Conjugation

variable {F H A : Type*} [Field F] [CommRing H] [HopfAlgebra F H] [CommRing A] [Algebra F A]

local notation "C" => HopfCotangent F H

/-- The actual Hopf adjoint action commutes with extension of point scalars. -/
theorem hopfAdjoint_postcompose {B : Type*} [CommRing B] [Algebra F B] (f : A →ₐ[F] B)
    (p : H →ₐ[F] A) (x : HopfLieVector F H A) :
    f.toLinearMap.comp (hopfAdjoint p x) =
      hopfAdjoint (f.comp p) (f.toLinearMap.comp x) := by
  apply LinearMap.ext
  intro c
  let z := hopfCotangentCoaction F H c
  change f ((LinearMap.mul' F A) (TensorProduct.map p.toLinearMap x z)) =
    (LinearMap.mul' F B) (TensorProduct.map (f.comp p).toLinearMap (f.toLinearMap.comp x) z)
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a v => simp only [TensorProduct.map_tmul, LinearMap.mul'_apply,
      AlgHom.toLinearMap_apply, AlgHom.comp_apply, LinearMap.comp_apply, map_mul]

/-- Pullback of conjugation sends an infinitesimal point to the
infinitesimal point of the adjoint-transformed tangent vector. -/
theorem hopfInfinitesimal_conjugation (p : H →ₐ[F] A) (y : HopfLieVector F H A) :
    (tensorPoint ((TrivSqZeroExt.inlAlgHom F A A).comp p) (hopfLieInfinitesimalPoint y)).comp
        (hopfConjugation F H) =
      hopfLieInfinitesimalPoint (hopfAdjoint p y) := by
  let q := tensorPoint ((TrivSqZeroExt.inlAlgHom F A A).comp p) (hopfLieInfinitesimalPoint y)
  have hf (z : H ⊗[F] H) : (q z).fst = tensorPoint p hopfPointOne z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TrivSqZeroExt.fst_zero]
    | add a b ha hb => simp only [map_add, TrivSqZeroExt.fst_add, ha, hb]
    | tmul a b =>
      change (tensorPoint ((TrivSqZeroExt.inlAlgHom F A A).comp p)
        (hopfLieInfinitesimalPoint y) (a ⊗ₜ[F] b)).fst = _
      simp only [tensorPoint_tmul, TrivSqZeroExt.fst_mul, AlgHom.comp_apply,
        TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.fst_inl, hopfLieInfinitesimalPoint_fst,
        hopfPointOne, AlgHom.comp_apply, Algebra.ofId_apply]
  let L := (LinearMap.mul' F A).comp (TensorProduct.map p.toLinearMap y)
  have hs (z : H ⊗[F] H) : (q z).snd = L ((hopfCotangentProjection F H).lTensor H z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TrivSqZeroExt.snd_zero]
    | add a b ha hb => simp only [map_add, TrivSqZeroExt.snd_add, ha, hb]
    | tmul a b =>
      change (tensorPoint ((TrivSqZeroExt.inlAlgHom F A A).comp p)
        (hopfLieInfinitesimalPoint y) (a ⊗ₜ[F] b)).snd = _
      rw [tensorPoint_tmul, DualNumber.snd_mul]
      change p a * y (hopfCotangentProjection F H b) +
        0 * algebraMap F A (Bialgebra.counitAlgHom F H b) = _
      rw [zero_mul, add_zero]
      rfl
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · change (q (hopfConjugation F H a)).fst =
      algebraMap F A (Bialgebra.counitAlgHom F H a)
    rw [hf]
    exact DFunLike.congr_fun (hopfConjugation_identity p) a
  · change (q (hopfConjugation F H a)).snd =
      hopfAdjoint p y (hopfCotangentProjection F H a)
    rw [hs]
    change L ((hopfCotangentProjection F H).lTensor H (hopfConjugation F H a)) =
      L (hopfCotangentCoaction F H (hopfCotangentProjection F H a))
    rw [hopfCotangentCoaction_proj]
    rfl

end Conjugation

section TangentConjugation

variable {F H A ι : Type*} [Field F] [CommRing H] [HopfAlgebra F H] [CommRing A] [Algebra F A]
  [Fintype ι] [DecidableEq ι]

local notation "C" => HopfCotangent F H

/-- The adjoint action is compatible with the group law on points. -/
theorem hopfAdjoint_mul (b : Basis ι F C) (p q : H →ₐ[F] A) (x : HopfLieVector F H A) :
    letI := hopfPointGroup (k := F) (H := H) (A := A)
    hopfAdjoint (p * q) x = hopfAdjoint p (hopfAdjoint q x) := by
  letI := hopfPointGroup (k := F) (H := H) (A := A)
  let φ := hopfPointMatrix (hopfAdjointMatrixUnit b) (hopfAdjointMatrix_comul b) (hopfAdjointMatrix_counit b)
    (A := A)
  have hM := congrArg Units.val (φ.map_mul p q)
  change (hopfAdjointMatrix b).map (p * q) =
    (hopfAdjointMatrix b).map p * (hopfAdjointMatrix b).map q at hM
  apply b.ext
  intro i
  have hL := hopfAdjoint_apply_basis b (p * q) x
  have hR := hopfAdjoint_apply_basis b p (hopfAdjoint q x)
  rw [hM, ← Matrix.mulVec_mulVec] at hL
  rw [hopfAdjoint_apply_basis b q x] at hR
  exact congrFun (hL.trans hR.symm) i

omit [DecidableEq ι] in
private theorem hopfAdjoint_constant_snd (b : Basis ι F C) (p : H →ₐ[F] A)
    (z : HopfLieVector F H (DualNumber A)) :
    (fun i => (hopfAdjoint ((TrivSqZeroExt.inlAlgHom F A A).comp p) z (b i)).snd) =
      (hopfAdjointMatrix b).map p *ᵥ (fun i => (z (b i)).snd) := by
  funext i
  have h := congrFun (hopfAdjoint_apply_basis b ((TrivSqZeroExt.inlAlgHom F A A).comp p) z) i
  change hopfAdjoint ((TrivSqZeroExt.inlAlgHom F A A).comp p) z (b i) = _ at h
  rw [h]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, TrivSqZeroExt.snd_sum,
    DualNumber.snd_mul, AlgHom.comp_apply, TrivSqZeroExt.inlAlgHom_apply,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_mul, add_zero]

/-- The orbit derivative at a conjugate vector is intertwined by the same
adjoint matrix over any coefficient algebra. -/
theorem hopfAdjointTangentMatrix_intertwines (b : Basis ι F C) (p : H →ₐ[F] A)
    (x : HopfLieVector F H A) :
    hopfAdjointTangentMatrix b (fun i => hopfAdjoint p x (b i)) * (hopfAdjointMatrix b).map p =
      (hopfAdjointMatrix b).map p * hopfAdjointTangentMatrix b (fun i => x (b i)) := by
  letI := hopfPointGroup (k := F) (H := H) (A := DualNumber A)
  let p₀ := (TrivSqZeroExt.inlAlgHom F A A).comp p
  apply Matrix.ext_of_mulVec_single
  intro j
  let v : ι → A := Pi.single j 1
  let y : HopfLieVector F H A := b.constr A v
  have hy (i : ι) : y (b i) = v i := b.constr_basis A v i
  have hMul : hopfLieInfinitesimalPoint (hopfAdjoint p y) * p₀ =
      p₀ * hopfLieInfinitesimalPoint y := by
    rw [← hopfInfinitesimal_conjugation p y, hopfConjugation_eval]
    change p₀ * hopfLieInfinitesimalPoint y * p₀⁻¹ * p₀ = _
    rw [mul_assoc _ p₀⁻¹ p₀, inv_mul_cancel, mul_one]
  have hX : hopfLieVector_toDual (hopfAdjoint p x) = hopfAdjoint p₀ (hopfLieVector_toDual x) :=
    hopfAdjoint_postcompose (TrivSqZeroExt.inlAlgHom F A A) p x
  have h := congrArg (fun w : H →ₐ[F] DualNumber A => hopfAdjoint w (hopfLieVector_toDual x)) hMul
  change hopfAdjoint (hopfLieInfinitesimalPoint (hopfAdjoint p y) * p₀) (hopfLieVector_toDual x) =
    hopfAdjoint (p₀ * hopfLieInfinitesimalPoint y) (hopfLieVector_toDual x) at h
  rw [hopfAdjoint_mul b, hopfAdjoint_mul b, ← hX] at h
  have hS := congrArg (fun f : HopfLieVector F H (DualNumber A) => fun i => (f (b i)).snd) h
  change (fun i => (hopfAdjoint (hopfLieInfinitesimalPoint (hopfAdjoint p y))
      (hopfLieVector_toDual (hopfAdjoint p x)) (b i)).snd) =
    (fun i => (hopfAdjoint p₀ (hopfAdjoint (hopfLieInfinitesimalPoint y)
      (hopfLieVector_toDual x)) (b i)).snd) at hS
  dsimp only [p₀] at hS
  rw [hopfAdjoint_constant_snd b] at hS
  simp only [hopfAdjoint_infinitesimal_snd b] at hS
  rw [hopfAdjoint_apply_basis b p y] at hS
  simpa only [hy, Matrix.mulVec_mulVec, v] using hS

/-- The whole characteristic polynomial of the adjoint orbit derivative
is an invariant under the actual group action. -/
theorem hopfAdjointTangentMatrix_charpoly_invariant (b : Basis ι F C) (p : H →ₐ[F] A)
    (x : HopfLieVector F H A) :
    (hopfAdjointTangentMatrix b (fun i => hopfAdjoint p x (b i))).charpoly =
      (hopfAdjointTangentMatrix b (fun i => x (b i))).charpoly := by
  let D' := hopfAdjointTangentMatrix b (fun i => hopfAdjoint p x (b i))
  let D := hopfAdjointTangentMatrix b (fun i => x (b i))
  let M : (Matrix ι ι A)ˣ := (hopfAdjointMatrixUnit b).map p.toRingHom.mapMatrix.toMonoidHom
  let P : (Matrix ι ι (Polynomial A))ˣ := M.map Polynomial.C.mapMatrix.toMonoidHom
  have hmap : (D'.map Polynomial.C) * P.val = P.val * (D.map Polynomial.C) := by
    have h : D' * M.val = M.val * D := hopfAdjointTangentMatrix_intertwines b p x
    have hm := congrArg (fun N : Matrix ι ι A => N.map Polynomial.C) h
    change (D' * M.val).map Polynomial.C = (M.val * D).map Polynomial.C at hm
    rwa [Matrix.map_mul, Matrix.map_mul] at hm
  have hChar : D'.charmatrix * P.val = P.val * D.charmatrix := by
    change (Matrix.scalar ι Polynomial.X - D'.map Polynomial.C) * P.val =
      P.val * (Matrix.scalar ι Polynomial.X - D.map Polynomial.C)
    rw [Matrix.sub_mul, Matrix.mul_sub]
    exact congrArg₂ (· - ·)
      (Matrix.scalar_commute (Polynomial.X : Polynomial A) (fun _ => Commute.all _ _) P.val).eq hmap
  have hd := congrArg Matrix.det hChar
  change (D'.charmatrix * P.val).det = (P.val * D.charmatrix).det at hd
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have hUnit : IsUnit P.val.det :=
    P.isUnit.map (Matrix.detMonoidHom : Matrix ι ι (Polynomial A) →* Polynomial A)
  exact (hUnit.mul_left_inj).mp (hd.trans (mul_comm _ _))

end TangentConjugation

end WideE
