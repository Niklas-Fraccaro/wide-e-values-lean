import WideE.InvariantIdeal
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Ring

/-! A full differential at a point over the identity makes a morphism into
an integral affine group dominant. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

variable {k H A : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

local notation "ε" => (Bialgebra.counitAlgHom k H)
local notation "Δ" => (Bialgebra.comulAlgHom k H)
local notation "π" => hopfCotangentProjection k H

private def derivationDualPoint (f : H →ₐ[k] A) (D : Derivation k A A) : H →ₐ[k] DualNumber A where
  toFun a := ⟨f a, D (f a)⟩
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one f
    · change D (f 1) = 0
      rw [map_one, D.map_one_eq_zero]
  map_zero' := by
    apply TrivSqZeroExt.ext
    · exact map_zero f
    · change D (f 0) = 0
      rw [map_zero, map_zero]
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · exact map_add f _ _
    · change D (f (a + b)) = D (f a) + D (f b)
      rw [map_add, map_add]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul f _ _
    · rw [DualNumber.snd_mul]
      change D (f (a * b)) = f a * D (f b) + D (f a) * f b
      rw [map_mul, D.leibniz, Algebra.id.smul_eq_mul, Algebra.id.smul_eq_mul, mul_comm (f b)]
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact f.commutes c
    · change D (f (algebraMap k H c)) = 0
      rw [f.commutes, D.map_algebraMap]

private theorem exists_infinitesimal_translate (f : H →ₐ[k] A) (D : Derivation k A A) :
    ∃ x : HopfLieVector k H A, derivationDualPoint f D =
      hopfPointMul ((TrivSqZeroExt.inlAlgHom k A A).comp f) (hopfLieInfinitesimalPoint x) := by
  letI : Group (H →ₐ[k] DualNumber A) := hopfPointGroup
  let g := (TrivSqZeroExt.inlAlgHom k A A).comp f
  let t := g⁻¹ * derivationDualPoint f D
  let fst := TrivSqZeroExt.fstHom k A A
  have hBase : fst.comp t = hopfPointOne := by
    change fst.comp (hopfPointMul (g.comp (hopfAntipodeAlgHom k H)) (derivationDualPoint f D)) = _
    rw [hopfPointMul_postcompose]
    rw [show fst.comp (g.comp (hopfAntipodeAlgHom k H)) = f.comp (hopfAntipodeAlgHom k H)
      from AlgHom.ext fun _ => rfl, show fst.comp (derivationDualPoint f D) = f from AlgHom.ext fun _ => rfl]
    exact hopfPointMul_inverse_left f
  let p : HopfInfinitesimalPoint k H A := ⟨t, DFunLike.congr_fun hBase⟩
  let x := (hopfInfinitesimalPointEquiv k H A).symm p
  have hx : hopfLieInfinitesimalPoint x = t := congrArg Subtype.val
    ((hopfInfinitesimalPointEquiv k H A).apply_symm_apply p)
  refine ⟨x, ?_⟩
  change derivationDualPoint f D = g * hopfLieInfinitesimalPoint x
  rw [hx, show t = g⁻¹ * derivationDualPoint f D from rfl, ← mul_assoc, mul_inv_cancel, one_mul]

private def invariantDerivativeTensor (D : hopfInvariantDerivations k H) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap.comp ((ε).toLinearMap.lTensor H) ∘ₗ D.val.toLinearMap.lTensor H

private theorem invariantDerivativeTensor_comul (D : hopfInvariantDerivations k H) (a : H) :
    invariantDerivativeTensor D (Δ a) = D.val a := by
  change TensorProduct.rid k H ((ε).toLinearMap.lTensor H (D.val.toLinearMap.lTensor H (Δ a))) = _
  rw [← D.prop a, show (ε).toLinearMap.lTensor H (Δ (D.val a)) =
    (TensorProduct.rid k H).symm (D.val a) from Coalgebra.lTensor_counit_comul _, LinearEquiv.apply_symm_apply]

private theorem invariantDerivativeTensor_tmul (D : hopfInvariantDerivations k H) (a b : H) :
    invariantDerivativeTensor D (a ⊗ₜ[k] b) = ε (D.val b) • a := rfl

variable {ι : Type*} [Fintype ι]

/-- Left translation expresses a derivation of the parameter ring as a
linear combination of evaluated invariant derivatives. -/
theorem exists_invariant_derivative_frame (b : Basis ι k (HopfCotangent k H))
    (f : H →ₐ[k] A) (D : Derivation k A A) :
    ∃ x : HopfLieVector k H A, ∀ a,
      D (f a) = ∑ i, x (b i) * f (((hopfLieVectorInvariantDerivations (b.coord i)).val) a) := by
  obtain ⟨x, hx⟩ := exists_infinitesimal_translate f D
  refine ⟨x, fun a => ?_⟩
  let g := (TrivSqZeroExt.inlAlgHom k A A).comp f
  let t := hopfLieInfinitesimalPoint x
  let δ (i : ι) := hopfLieVectorInvariantDerivations (b.coord i)
  have h (z : H ⊗[k] H) :
      (tensorPoint g t z).snd = ∑ i, x (b i) * f (invariantDerivativeTensor (δ i) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw =>
      simp only [map_add, TrivSqZeroExt.snd_add, hz, hw, mul_add, Finset.sum_add_distrib]
    | tmul a b' =>
      rw [tensorPoint_tmul, DualNumber.snd_mul]
      change f a * x (π b') + 0 * (t b').fst = _
      rw [zero_mul, add_zero]
      have hr : x (π b') = ∑ i, (b.coord i (π b')) • x (b i) := by
        conv_lhs => rw [← b.sum_repr (π b')]
        simp only [map_sum, map_smul, Basis.coord_apply]
      rw [hr, Finset.mul_sum]
      simp only [invariantDerivativeTensor_tmul, δ, hopfLieVectorInvariantDerivations_counit, map_smul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Algebra.smul_def]
      ring
  change (derivationDualPoint f D a).snd = _
  rw [hx]
  change (tensorPoint g t (Δ a)).snd = _
  rw [h]
  simp only [invariantDerivativeTensor_comul, δ]

variable [CharZero k] [IsDomain H] [Algebra.FiniteType k H] [IsDomain A] [DecidableEq ι]

/-- Independent tangent directions over the identity certify injectivity of the
coordinate map into the parameter algebra. -/
theorem injective_hopfMap_of_tangent_jacobian
    (b : Basis ι k (HopfCotangent k H)) (f : H →ₐ[k] A)
    (q : A →ₐ[k] k) (hq : q.comp f = ε)
    (s : ι → H) (hs : ∀ i, π (s i) = b i)
    (D : ι → Derivation k A A)
    (hJ : (Matrix.of fun r i => q (D r (f (s i)))).det ≠ 0) :
    Function.Injective f := by
  classical
  choose x hx using fun r => exists_invariant_derivative_frame b f (D r)
  let δ (i : ι) := hopfLieVectorInvariantDerivations (b.coord i)
  let J : Matrix ι ι A := Matrix.of fun r i => x r (b i)
  have hQ (r i : ι) : q (D r (f (s i))) = q (J r i) := by
    rw [hx r, map_sum]
    simp only [map_mul, ← AlgHom.comp_apply q f, hq,
      hopfLieVectorInvariantDerivations_counit, hs, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl
  have hJ₀ : J.det ≠ 0 := by
    intro h₀
    apply hJ
    have h : Matrix.of (fun r i => q (D r (f (s i)))) = q.toRingHom.mapMatrix J :=
      Matrix.ext hQ
    rw [h, ← RingHom.map_det, h₀, map_zero]
  apply (RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr
  apply hopfInvariantIdeal_eq_bot (k := k)
  · intro a ha
    change f a = 0 at ha
    change ε a = 0
    rw [← hq, AlgHom.comp_apply, ha, map_zero]
  · intro E a ha
    change f a = 0 at ha
    change f (E.val a) = 0
    let y : ι → A := fun i => f ((δ i).val a)
    have hJy : J *ᵥ y = 0 := by
      funext r
      change ∑ i, x r (b i) * f ((δ i).val a) = 0
      rw [← hx r a, ha, map_zero]
    have hdety : J.det • y = 0 := by
      have h := congrArg (fun z : ι → A => J.adjugate *ᵥ z) hJy
      change J.adjugate *ᵥ (J *ᵥ y) = J.adjugate *ᵥ 0 at h
      rwa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec_assoc,
        Matrix.one_mulVec, Matrix.mulVec_zero] at h
    have hy (i : ι) : f ((δ i).val a) = 0 :=
      (mul_eq_zero.mp (congrFun hdety i)).resolve_left hJ₀
    let v := (hopfLieVectorInvariantDerivations (k := k) (H := H)).symm E
    have hv : v = ∑ i, v (b i) • b.coord i := by
      apply b.ext
      intro i
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Basis.coord_apply, Basis.repr_self,
        Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have hE : E = ∑ i, v (b i) • δ i := by
      rw [← (hopfLieVectorInvariantDerivations (k := k) (H := H)).apply_symm_apply E]
      conv_lhs => change hopfLieVectorInvariantDerivations v; rw [hv, map_sum]
      simp only [map_smul, δ]
    let ev (F : hopfInvariantDerivations k H) : A := f (F.val a)
    let evAdd : hopfInvariantDerivations k H →+ A := {
      toFun := ev
      map_add' F G := map_add f _ _
      map_zero' := map_zero f }
    change evAdd E = 0
    rw [hE, map_sum]
    exact Finset.sum_eq_zero fun i _ => by
      change f (v (b i) • (δ i).val a) = 0
      rw [map_smul, hy, smul_zero]

end WideE
