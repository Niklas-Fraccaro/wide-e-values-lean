import WideE.GaloisKernelReduction
import WideE.IntegralTorsorReducedGroup
import WideE.RegularKernelTorsor
import WideE.UnitriangularConnected

/-! A faithfully flat affine group morphism is the regular torsor of its actual kernel. -/

noncomputable section

open scoped TensorProduct
open TensorProduct

namespace WideE

section Translation

variable {k Q H : Type*} [Field k] [CommRing Q] [CommRing H] [HopfAlgebra k Q] [HopfAlgebra k H]
  (j : Q →ₐc[k] H)

local notation "ΔQ" => Bialgebra.comulAlgHom k Q
local notation "ΔH" => Bialgebra.comulAlgHom k H
local notation "εQ" => Bialgebra.counitAlgHom k Q
local notation "I" => hopfKernelIdeal j

private theorem hopfTranslationChart_natural (z : Q ⊗[k] Q) :
    let f : Q →ₐ[k] H := j
    hopfTranslationChart k H (Algebra.TensorProduct.map f f z) =
      Algebra.TensorProduct.map f f (hopfTranslationChart k Q z) := by
  intro f
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul]
    change ((f x) ⊗ₜ[k] (1 : H)) * ΔH (f y) =
      Algebra.TensorProduct.map f f ((x ⊗ₜ[k] (1 : Q)) * ΔQ y)
    rw [map_mul, Algebra.TensorProduct.map_tmul, map_one,
      show ΔH (f y) = Algebra.TensorProduct.map f f (ΔQ y) from
        (DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom j) y).symm]

private theorem hopfTranslationChart_symm_natural (z : Q ⊗[k] Q) :
    let f : Q →ₐ[k] H := j
    (hopfTranslationChart k H).symm (Algebra.TensorProduct.map f f z) =
      Algebra.TensorProduct.map f f ((hopfTranslationChart k Q).symm z) := by
  intro f
  apply (hopfTranslationChart k H).injective
  rw [AlgEquiv.apply_symm_apply, hopfTranslationChart_natural j, AlgEquiv.apply_symm_apply]

private theorem hopfKernel_fixed (a : Q) :
    Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I) (ΔH (j a)) =
      (j a) ⊗ₜ[k] (1 : H ⧸ I) := by
  let J := H ⧸ I
  let A := H ⊗[k] J
  let p : H →ₐ[k] J := Ideal.Quotient.mkₐ k I
  let l : H →ₐ[k] A := Algebra.TensorProduct.includeLeft
  let r : J →ₐ[k] A := Algebra.TensorProduct.includeRight
  have hTensor : tensorPoint l (r.comp p) = Algebra.TensorProduct.map (AlgHom.id k H) p := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [tensorPoint_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change (x ⊗ₜ[k] (1 : J)) * ((1 : H) ⊗ₜ[k] p y) = x ⊗ₜ[k] p y
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  letI := hopfPointGroup (k := k) (H := H) (A := A)
  letI := hopfPointGroup (k := k) (H := Q) (A := A)
  let f := hopfPointPrecompose (A := A) j
  have hr : f (r.comp p) = 1 :=
    (congrArg (fun q => r.comp q) (hopfKernel_mk_precompose j)).trans (hopfPointOne_postcompose r)
  have h : f (l * r.comp p) = f l := by rw [map_mul, hr, mul_one]
  have h' := DFunLike.congr_fun h a
  change tensorPoint l (r.comp p) (ΔH (j a)) = l (j a) at h'
  rw [hTensor] at h'
  exact h'

private theorem kernelRelativeTensor_diagonal (z : Q ⊗[k] Q) :
    let f : Q →ₐ[k] H := j
    letI : Algebra Q H := f.toRingHom.toAlgebra
    letI : IsScalarTower k Q H := IsScalarTower.of_algHom f
    kernelRelativeTensor (Q := Q) (Algebra.TensorProduct.map f f z) =
      (1 : H) ⊗ₜ[Q] f (LinearMap.mul' k Q z) := by
  intro f
  letI : Algebra Q H := f.toRingHom.toAlgebra
  letI : IsScalarTower k Q H := IsScalarTower.of_algHom f
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, tmul_add]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, kernelRelativeTensor_tmul, LinearMap.mul'_apply, map_mul]
    simpa only [Algebra.smul_def, mul_one] using (TensorProduct.smul_tmul a (1 : H) (f b))

private theorem regularKernel_translated_counit [Algebra.FiniteType k H] (a : Q) :
    let f : Q →ₐ[k] H := j
    letI : Algebra Q H := f.toRingHom.toAlgebra
    letI : IsScalarTower k Q H := IsScalarTower.of_algHom f
    kernelRelativeTensor (Q := Q) ((regularAffineHopfTorsor k H).chart ((1 : H) ⊗ₜ[k] f a)) =
      (1 : H) ⊗ₜ[Q] f (algebraMap k Q (εQ a)) := by
  intro f
  letI : Algebra Q H := f.toRingHom.toAlgebra
  letI : IsScalarTower k Q H := IsScalarTower.of_algHom f
  let T := regularAffineHopfTorsor k H
  have hChart (z : H ⊗[k] H) : T.chart z = (hopfTranslationChart k H).symm z := by
    apply (hopfTranslationChart k H).injective
    change T.chart.symm (T.chart z) = (hopfTranslationChart k H) ((hopfTranslationChart k H).symm z)
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply]
  change kernelRelativeTensor (Q := Q) (T.chart ((1 : H) ⊗ₜ[k] f a)) = _
  have h₁ : Algebra.TensorProduct.map f f ((1 : Q) ⊗ₜ[k] a) = (1 : H) ⊗ₜ[k] f a := by
    rw [Algebra.TensorProduct.map_tmul, map_one]
  rw [hChart, ← h₁, hopfTranslationChart_symm_natural j, kernelRelativeTensor_diagonal j]
  have h₂ : (hopfTranslationChart k Q).symm ((1 : Q) ⊗ₜ[k] a) =
      ((1 : Q) ⊗ₜ[k] (1 : Q)) *
        (HopfAlgebra.antipode (R := k) (A := Q)).rTensor Q (ΔQ a) := rfl
  rw [h₂, ← Algebra.TensorProduct.one_def, one_mul]
  change (1 : H) ⊗ₜ[Q] f (LinearMap.mul' k Q
    ((HopfAlgebra.antipode (R := k) (A := Q)).rTensor Q (Coalgebra.comul (R := k) a))) = _
  rw [HopfAlgebra.mul_antipode_rTensor_comul_apply]
  rfl

end Translation

section Torsor

universe u

variable {k Q H : Type u} [Field k] [CommRing Q] [CommRing H]
  [HopfAlgebra k Q] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- The total group is a torsor over the quotient for the actual kernel. -/
def regularKernelTorsor (j : Q →ₐc[k] H)
    (hj : letI : Algebra Q H := (j : Q →ₐ[k] H).toRingHom.toAlgebra; Module.FaithfullyFlat Q H) :
    letI : Algebra Q H := (j : Q →ₐ[k] H).toRingHom.toAlgebra
    letI : IsScalarTower k Q H := IsScalarTower.of_algHom (j : Q →ₐ[k] H)
    letI := (hopfKernelIdeal_isHopf j).quotientHopf
    AffineHopfTorsor k Q H (H ⧸ hopfKernelIdeal j) := by
  let f : Q →ₐ[k] H := j
  letI : Algebra Q H := f.toRingHom.toAlgebra
  letI : IsScalarTower k Q H := IsScalarTower.of_algHom f
  let I := hopfKernelIdeal j
  let J := H ⧸ I
  letI : HopfAlgebra k J := (hopfKernelIdeal_isHopf j).quotientHopf
  let p := (hopfKernelIdeal_isHopf j).quotientBialgHom
  let T := regularAffineHopfTorsor k H
  have hp : Function.Surjective p := Ideal.Quotient.mk_surjective
  have hfix (a : Q) : T.kernelAction p (algebraMap Q H a) = algebraMap Q H a ⊗ₜ[k] (1 : J) :=
    hopfKernel_fixed j a
  refine ⟨T.restrictCoactionOver p hfix, T.kernelAction_coassociative p, T.kernelAction_counital p,
    T.kernel_canonical_bijective_of_kills p hp hfix ?_, hj,
    Algebra.FiniteType.of_surjective inferInstance (p : H →ₐ[k] J) hp⟩
  change (RingHom.ker (p : H →ₐ[k] J).toRingHom).map
      (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H) ≤
    RingHom.ker ((kernelRelativeTensor (Q := Q)).comp T.chart.toAlgHom)
  rw [show RingHom.ker (p : H →ₐ[k] J).toRingHom = I from Ideal.mk_ker]
  change (((RingHom.ker (Bialgebra.counitAlgHom k Q).toRingHom).map f.toRingHom).map
    (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H)) ≤ _
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  intro a ha
  change kernelRelativeTensor (Q := Q) (T.chart ((1 : H) ⊗ₜ[k] f a)) = 0
  rw [regularKernel_translated_counit j,
    show Bialgebra.counitAlgHom k Q a = 0 from ha, map_zero, map_zero, tmul_zero]

/-- An integral affine group in characteristic zero has a reduced kernel under
the indicated faithfully flat quotient. -/
theorem hopfKernel_isReduced_of_domain [CharZero k] [IsDomain H]
    (j : Q →ₐc[k] H) (hi : Function.Injective j)
    (hj : letI : Algebra Q H := (j : Q →ₐ[k] H).toRingHom.toAlgebra; Module.FaithfullyFlat Q H) :
    IsReduced (H ⧸ hopfKernelIdeal j) := by
  let f : Q →ₐ[k] H := j
  letI : Algebra Q H := f.toRingHom.toAlgebra
  letI : IsScalarTower k Q H := IsScalarTower.of_algHom f
  letI : IsDomain Q := Function.Injective.isDomain f hi
  letI : CharZero Q := Algebra.charZero_of_charZero k Q
  letI := (hopfKernelIdeal_isHopf j).quotientHopf
  exact (regularKernelTorsor j hj).group_isReduced_of_integral_total

end Torsor

section BlockKernel

universe u

variable {k H : Type u} {β : Type*} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [IsDomain H]
  [HopfAlgebra k H] [LinearOrder β] {n : ℕ}

/-- The connected block kernel of an integral affine group has an integral coordinate algebra. -/
theorem blockDiagonalKernel_isDomain (b : Fin n → β) (M : Matrix (Fin n) (Fin n) H)
    (hD : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0)
    (hUpper : M.BlockTriangular b) (hb : Monotone b)
    (hGen : Algebra.adjoin k (Set.range fun ij : Fin n × Fin n => M ij.1 ij.2) = ⊤) :
    IsDomain (H ⧸ blockDiagonalKernelIdeal b M hD hUpper) := by
  letI : Algebra.FiniteType k H := ⟨Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, hGen⟩⟩
  let Q := blockDiagonalAlgebra (k := k) b M
  letI := (blockDiagonalAlgebra_isHopf b M hD hUpper).hopfAlgebra
  let j := blockDiagonalQuotientMap b M hD hUpper
  let I := hopfKernelIdeal j
  letI := (hopfKernelIdeal_isHopf j).quotientHopf
  letI : IsReduced (H ⧸ I) := hopfKernel_isReduced_of_domain j Subtype.val_injective
    (blockDiagonalQuotient_faithfullyFlat b M hD hUpper)
  letI : ConnectedSpace (PrimeSpectrum (H ⧸ I)) :=
    blockDiagonalKernel_connectedSpace M b hb hD he hUpper hGen
  letI : Algebra.FiniteType k (H ⧸ I) := Algebra.FiniteType.of_surjective inferInstance
    (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ_surjective k I)
  exact hopfDomain_of_connected_reduced (k := k) (H := H ⧸ I)

end BlockKernel

end WideE
