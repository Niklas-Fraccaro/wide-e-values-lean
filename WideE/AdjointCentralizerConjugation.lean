import WideE.AdjointCovariance
import WideE.AdjointToricDescent
import WideE.BigCellCentralizer

/-! Conjugation transports the actual Hopf quotients of adjoint stabilizers. -/

noncomputable section

open scoped TensorProduct Matrix Ideal

namespace WideE

section ConjugationMap

variable {k H A : Type*} [Field k] [CommRing H] [HopfAlgebra k H] [CommRing A] [Algebra k A]

local notation "ε" => Bialgebra.counitAlgHom k H
local notation "Δ" => Bialgebra.comulAlgHom k H

/-- The pullback of conjugation by a rational point. -/
def hopfConjugateBy (p : H →ₐ[k] k) : H →ₐ[k] H :=
  (tensorPoint ((Algebra.ofId k H).comp p) (AlgHom.id k H)).comp (hopfConjugation k H)

theorem hopfConjugateBy_eval (p : H →ₐ[k] k) (q : H →ₐ[k] A) :
    letI := hopfPointGroup (k := k) (H := H) (A := A)
    q.comp (hopfConjugateBy p) =
      ((Algebra.ofId k A).comp p) * q * ((Algebra.ofId k A).comp p)⁻¹ := by
  letI := hopfPointGroup (k := k) (H := H) (A := A)
  have h : q.comp (tensorPoint ((Algebra.ofId k H).comp p) (AlgHom.id k H)) =
      tensorPoint ((Algebra.ofId k A).comp p) q := by
    apply Algebra.TensorProduct.ext'
    intro a b
    rw [AlgHom.comp_apply, tensorPoint_tmul, tensorPoint_tmul, map_mul, AlgHom.id_apply]
    exact congrArg (· * q b) (q.commutes (p a))
  rw [hopfConjugateBy, ← AlgHom.comp_assoc, h, hopfConjugation_eval]

private theorem hopfConjugateBy_preserves_pointMul (p : H →ₐ[k] k)
    (q r : H →ₐ[k] A) :
    (hopfPointMul q r).comp (hopfConjugateBy p) =
      hopfPointMul (q.comp (hopfConjugateBy p)) (r.comp (hopfConjugateBy p)) := by
  letI := hopfPointGroup (k := k) (H := H) (A := A)
  change (q * r).comp (hopfConjugateBy p) =
    q.comp (hopfConjugateBy p) * r.comp (hopfConjugateBy p)
  rw [hopfConjugateBy_eval, hopfConjugateBy_eval, hopfConjugateBy_eval]
  simp only [mul_assoc, inv_mul_cancel_left]

private theorem hopfConjugateBy_preserves_counit (p : H →ₐ[k] k) :
    (ε).comp (hopfConjugateBy p) = ε := by
  letI := hopfPointGroup (k := k) (H := H) (A := k)
  change (1 : H →ₐ[k] k).comp (hopfConjugateBy p) = 1
  rw [hopfConjugateBy_eval, mul_one, mul_inv_cancel]

private theorem hopfConjugateBy_preserves_comul (p : H →ₐ[k] k) :
    (Δ).comp (hopfConjugateBy p) =
      (Algebra.TensorProduct.map (hopfConjugateBy p) (hopfConjugateBy p)).comp (Δ) := by
  let l : H →ₐ[k] H ⊗[k] H := Algebra.TensorProduct.includeLeft
  let r : H →ₐ[k] H ⊗[k] H := Algebra.TensorProduct.includeRight
  let c := hopfConjugateBy p
  have hId : tensorPoint l r = AlgHom.id k (H ⊗[k] H) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    rw [tensorPoint_tmul, AlgHom.id_apply]
    change (a ⊗ₜ[k] (1 : H)) * ((1 : H) ⊗ₜ[k] b) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hD : hopfPointMul l r = Δ := by rw [hopfPointMul, hId, AlgHom.id_comp]
  have hC : tensorPoint (l.comp c) (r.comp c) = Algebra.TensorProduct.map c c := by
    apply Algebra.TensorProduct.ext'
    intro a b
    rw [tensorPoint_tmul, Algebra.TensorProduct.map_tmul]
    change (c a ⊗ₜ[k] (1 : H)) * ((1 : H) ⊗ₜ[k] c b) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  calc
    (Δ).comp c = (hopfPointMul l r).comp c := by rw [hD]
    _ = hopfPointMul (l.comp c) (r.comp c) := hopfConjugateBy_preserves_pointMul p l r
    _ = (Algebra.TensorProduct.map c c).comp (Δ) := by rw [hopfPointMul, hC]

/-- Conjugation by a rational point is a morphism of the actual coordinate bialgebra. -/
def hopfConjugateByBialgHom (p : H →ₐ[k] k) : H →ₐc[k] H :=
  BialgHom.ofAlgHom (hopfConjugateBy p)
    (LinearMap.ext fun a => DFunLike.congr_fun (hopfConjugateBy_preserves_counit p) a)
    (LinearMap.ext fun a => DFunLike.congr_fun (hopfConjugateBy_preserves_comul p).symm a)

private theorem hopfConjugateBy_inverse_comp_point (p : H →ₐ[k] k) (q : H →ₐ[k] A) :
    letI := hopfPointGroup (k := k) (H := H) (A := k)
    (q.comp (hopfConjugateBy p⁻¹)).comp (hopfConjugateBy p) = q := by
  letI := hopfPointGroup (k := k) (H := H) (A := k)
  letI := hopfPointGroup (k := k) (H := H) (A := A)
  let c := (Algebra.ofId k A).comp p
  have hInv : (Algebra.ofId k A).comp p⁻¹ = c⁻¹ := AlgHom.ext fun _ => rfl
  rw [hopfConjugateBy_eval p, hopfConjugateBy_eval p⁻¹, hInv, inv_inv]
  change c * (c⁻¹ * q * c) * c⁻¹ = q
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

theorem hopfConjugateBy_inverse_comp (p : H →ₐ[k] k) :
    letI := hopfPointGroup (k := k) (H := H) (A := k)
    (hopfConjugateBy p⁻¹).comp (hopfConjugateBy p) = AlgHom.id k H := by
  simpa only [AlgHom.id_comp] using hopfConjugateBy_inverse_comp_point p (AlgHom.id k H)

/-- The conjugation pullback is surjective, with the pullback at the inverse
point furnishing a right inverse. -/
theorem hopfConjugateBy_surjective (p : H →ₐ[k] k) : Function.Surjective (hopfConjugateBy p) := by
  letI := hopfPointGroup (k := k) (H := H) (A := k)
  intro a
  refine ⟨hopfConjugateBy p⁻¹ a, ?_⟩
  have h := hopfConjugateBy_inverse_comp p⁻¹
  rw [inv_inv] at h
  exact DFunLike.congr_fun h a

end ConjugationMap

section StabilizerAction

variable {k H A η : Type*} [Field k] [CommRing H] [HopfAlgebra k H] [CommRing A] [Algebra k A]
  [Fintype η] [DecidableEq η]

/-- The identity group point acts trivially on every tangent vector. -/
theorem hopfAdjoint_identity_point (b : Basis η k (HopfCotangent k H)) (v : HopfLieVector k H A) :
    hopfAdjoint (hopfPointOne : H →ₐ[k] A) v = v := by
  letI : Group (H →ₐ[k] A) := hopfPointGroup
  let ρ := hopfPointMatrix (A := A) (hopfAdjointMatrixUnit b)
    (hopfAdjointMatrix_comul b) (hopfAdjointMatrix_counit b)
  have hM : (hopfAdjointMatrix b).map (hopfPointOne : H →ₐ[k] A) = 1 :=
    congrArg Units.val (map_one ρ)
  have h := hopfAdjoint_apply_basis b (hopfPointOne : H →ₐ[k] A) v
  rw [hM, Matrix.one_mulVec] at h
  exact b.ext fun i => congrFun h i

private theorem hopfAdjoint_conjugate_fixed (b : Basis η k (HopfCotangent k H))
    (g p : H →ₐ[k] A) (x : HopfLieVector k H A) (hp : hopfAdjoint p x = x) :
    letI := hopfPointGroup (k := k) (H := H) (A := A)
    hopfAdjoint (g * p * g⁻¹) (hopfAdjoint g x) = hopfAdjoint g x := by
  letI := hopfPointGroup (k := k) (H := H) (A := A)
  rw [hopfAdjoint_mul b (g * p) g⁻¹, hopfAdjoint_mul b g p, ← hopfAdjoint_mul b g⁻¹ g, inv_mul_cancel]
  change hopfAdjoint g (hopfAdjoint p (hopfAdjoint (hopfPointOne : H →ₐ[k] A) x)) = _
  rw [hopfAdjoint_identity_point b x, hp]

private theorem hopfConjugateBy_centralizer_point (b : Basis η k (HopfCotangent k H))
    (p : H →ₐ[k] k) (x y : HopfLieVector k H k) (hx : hopfAdjoint p y = x)
    (q : H →ₐ[k] A)
    (hq : hopfAdjoint q ((Algebra.ofId k A).toLinearMap.comp y) =
      (Algebra.ofId k A).toLinearMap.comp y) :
    hopfAdjoint (q.comp (hopfConjugateBy p)) ((Algebra.ofId k A).toLinearMap.comp x) =
      (Algebra.ofId k A).toLinearMap.comp x := by
  letI := hopfPointGroup (k := k) (H := H) (A := A)
  let g := (Algebra.ofId k A).comp p
  let yA := (Algebra.ofId k A).toLinearMap.comp y
  have heq := (hopfAdjoint_postcompose (Algebra.ofId k A) p y).symm
  change hopfAdjoint g yA = (Algebra.ofId k A).toLinearMap.comp (hopfAdjoint p y) at heq
  rw [hx] at heq
  rw [hopfConjugateBy_eval p q, ← heq]
  exact hopfAdjoint_conjugate_fixed b g q yA hq

end StabilizerAction

section Quotients

variable {k H η : Type*} [Field k] [CommRing H] [HopfAlgebra k H] [Fintype η] [DecidableEq η]

set_option maxHeartbeats 1200000 in
/-- Conjugate Lie vectors have bialgebra-isomorphic actual centralizer quotients. -/
def bialgEquiv_hopfAdjointCentralizer_conjugate (b : Basis η k (HopfCotangent k H))
    (p : H →ₐ[k] k) (x y : HopfLieVector k H k) (hx : hopfAdjoint p y = x) :
    letI := (hopfAdjointCentralizerIdeal_isHopf b x).quotientHopf
    letI := (hopfAdjointCentralizerIdeal_isHopf b y).quotientHopf
    (H ⧸ hopfAdjointCentralizerIdeal b x) ≃ₐc[k] (H ⧸ hopfAdjointCentralizerIdeal b y) := by
  let Ix := hopfAdjointCentralizerIdeal b x
  let Iy := hopfAdjointCentralizerIdeal b y
  let Qx := H ⧸ Ix
  let Qy := H ⧸ Iy
  let Jx := hopfAdjointCentralizerIdeal_isHopf b x
  let Jy := hopfAdjointCentralizerIdeal_isHopf b y
  letI : HopfAlgebra k Qx := Jx.quotientHopf
  letI : HopfAlgebra k Qy := Jy.quotientHopf
  let jx : H →ₐ[k] Qx := Ideal.Quotient.mkₐ k Ix
  let jy : H →ₐ[k] Qy := Ideal.Quotient.mkₐ k Iy
  let f : H →ₐc[k] Qy := Jy.quotientBialgHom.comp (hopfConjugateByBialgHom p)
  have hf : Function.Surjective f :=
    (Ideal.Quotient.mkₐ_surjective k Iy).comp (hopfConjugateBy_surjective p)
  letI := hopfPointGroup (k := k) (H := H) (A := k)
  have hy : hopfAdjoint p⁻¹ x = y := by
    rw [← hx, ← hopfAdjoint_mul b p⁻¹ p, inv_mul_cancel]
    exact hopfAdjoint_identity_point b y
  have hxQ :
      hopfAdjoint jx ((Algebra.ofId k Qx).toLinearMap.comp x) =
        (Algebra.ofId k Qx).toLinearMap.comp x :=
    ((hopfAdjointCentralizerPoints (A := Qx) b x) (AlgHom.id k Qx)).prop
  have hyQ :
      hopfAdjoint jy ((Algebra.ofId k Qy).toLinearMap.comp y) =
        (Algebra.ofId k Qy).toLinearMap.comp y :=
    ((hopfAdjointCentralizerPoints (A := Qy) b y) (AlgHom.id k Qy)).prop
  let ex := hopfAdjointCentralizerPoints (A := Qy) b x
  let ey := hopfAdjointCentralizerPoints (A := Qx) b y
  let zx : {q : H →ₐ[k] Qy // hopfAdjoint q ((Algebra.ofId k Qy).toLinearMap.comp x) =
      (Algebra.ofId k Qy).toLinearMap.comp x} := ⟨jy.comp (hopfConjugateBy p),
        hopfConjugateBy_centralizer_point b p x y hx jy hyQ⟩
  let zy : {q : H →ₐ[k] Qx // hopfAdjoint q ((Algebra.ofId k Qx).toLinearMap.comp y) =
      (Algebra.ofId k Qx).toLinearMap.comp y} := ⟨jx.comp (hopfConjugateBy p⁻¹),
        hopfConjugateBy_centralizer_point b p⁻¹ y x hy jx hxQ⟩
  have hqx : (ex.symm zx).comp jx = (f : H →ₐ[k] Qy) :=
    congrArg Subtype.val (ex.apply_symm_apply zx)
  have hqy : (ey.symm zy).comp jy = jx.comp (hopfConjugateBy p⁻¹) :=
    congrArg Subtype.val (ey.apply_symm_apply zy)
  have hInv : (ey.symm zy).comp (f : H →ₐ[k] Qy) = jx := by
    change (ey.symm zy).comp (jy.comp (hopfConjugateBy p)) = jx
    rw [← AlgHom.comp_assoc, hqy, AlgHom.comp_assoc, hopfConjugateBy_inverse_comp, AlgHom.comp_id]
  have hKer : Ix = RingHom.ker (f : H →ₐ[k] Qy).toRingHom := by
    apply le_antisymm
    · intro a ha
      change (f : H →ₐ[k] Qy) a = 0
      rw [← hqx, AlgHom.comp_apply, show jx a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    · intro a ha
      change (f : H →ₐ[k] Qy) a = 0 at ha
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change jx a = 0
      rw [← hInv, AlgHom.comp_apply, ha, map_zero]
  exact bialgEquiv_quotientOfKerEq Jx f hf hKer

end Quotients

end WideE
