import WideE.HopfCartanTorus
import WideE.HopfLieCartan
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.Basis.Prod

/-! The Cartan subalgebra of a semisimple ideal and the center lie in a split torus. -/

noncomputable section

open scoped Matrix TensorProduct
open LieAlgebra LieModule Module

namespace WideE

section CentralComplement

variable {k L : Type*} [Field k] [IsAlgClosed k] [LieRing L] [LieAlgebra k L]
  [FiniteDimensional k L]

private theorem ad_add_center_isSemisimple (S : LieIdeal k L) (hC : IsCompl S (center k L))
    (x : S) (z : center k L) (h : (ad k S x).IsSemisimple) :
    (ad k L ((x : L) + (z : L))).IsSemisimple := by
  letI : FiniteDimensional k S := FiniteDimensional.of_injective S.toSubmodule.subtype
    Subtype.val_injective
  letI : FiniteDimensional k (center k L) := FiniteDimensional.of_injective
    (center k L).toSubmodule.subtype Subtype.val_injective
  obtain ⟨b, d, hb⟩ := exists_eigenbasis_of_isSemisimple (ad k S x) h
  let Z := center k L
  let f := Submodule.prodEquivOfIsCompl S.toSubmodule Z.toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr hC)
  let c := finBasis k Z
  let B := (b.prod c).map f
  have hLeft (i : Fin (finrank k S)) : B (Sum.inl i) = (b i : L) := by
    simp only [B, Basis.map_apply, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
      LinearMap.inl_apply, f, Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
    change (b i : L) + (0 : L) = _
    exact add_zero _
  have hRight (j : Fin (finrank k Z)) : B (Sum.inr j) = (c j : L) := by
    simp only [B, Basis.map_apply, Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
      LinearMap.inr_apply, f, Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]
    change (0 : L) + (c j : L) = _
    exact zero_add _
  apply isSemisimple_of_eigenbasis _ B (Sum.elim d fun _ => 0)
  rintro (i | j)
  · rw [hLeft, Sum.elim_inl, ad_apply, add_lie, ← lie_skew (z : L), z.property, neg_zero, add_zero]
    exact congrArg Subtype.val (hb i)
  · rw [hRight, Sum.elim_inr, zero_smul, ad_apply]
    exact (c j).property _

omit [IsAlgClosed k] [FiniteDimensional k L] in
private theorem lie_add_center_add_center (x y : L) (z w : center k L) :
    ⁅x + (z : L), y + (w : L)⁆ = ⁅x, y⁆ := by
  have hz : ⁅(z : L), y + (w : L)⁆ = 0 := by
    rw [← lie_skew (z : L), z.property, neg_zero]
  rw [add_lie, lie_add, w.property, add_zero, hz, add_zero]

omit [IsAlgClosed k] [FiniteDimensional k L] in
/-- A direction in the Cartan subalgebra of the semisimple factor together with a central part. -/
def cartanCenterDirection {S : LieIdeal k L} (C : LieSubalgebra k S)
    (x : C) (z : center k L) : L := ((x : S) : L) + (z : L)

end CentralComplement

section Torus

variable {k H ι : Type*} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H]
  [HopfAlgebra k H] [Algebra.FiniteType k H] [Fintype ι] [DecidableEq ι]

local notation "𝔤" => (hopfInvariantDerivations k H)

set_option maxHeartbeats 900000 in
/-- In the reductive situation, the actual split torus contains every direction of the
chosen Cartan subalgebra together with the center. -/
theorem exists_diagonalTorus_of_reductiveCartan (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (hZ : ∀ x ∈ center k 𝔤, IsNilpotent (hopfLieMatrix U.val x) → x = 0)
    (S : LieIdeal k 𝔤) [IsKilling k S] (hC : IsCompl S (center k 𝔤))
    (C : LieSubalgebra k S) [C.IsCartanSubalgebra] :
    ∃ (l m : ℕ) (P : (Matrix ι ι k)ˣ) (d : ι → (Fin l ⊕ Fin m) → k)
      (f : H →ₐc[k] diagonalWeightAlgebra k d),
      Function.Surjective f ∧
      (∀ i j, f ((conjugateMatrixUnit P U).val i j) = if i = j then diagonalWeightMonomial k d i else 0) ∧
      (∀ (x : C) (z : center k 𝔤), ∃ v : hopfInvariantDerivations k (diagonalWeightAlgebra k d),
        hopfInvariantDerivationsMap f v = cartanCenterDirection C x z) ∧
      ∃ n : ℕ, Nonempty (Basis (Fin n) ℤ (diagonalCharacterLattice d)) := by
  letI := hopfCotangent_finiteDimensional k H
  letI : FiniteDimensional k 𝔤 := FiniteDimensional.of_surjective
    (hopfLieVectorInvariantDerivations (k := k) (H := H)).toLinearMap
    (hopfLieVectorInvariantDerivations (k := k) (H := H)).surjective
  letI : FiniteDimensional k S := FiniteDimensional.of_injective S.toSubmodule.subtype
    Subtype.val_injective
  letI : FiniteDimensional k C := FiniteDimensional.of_injective C.toSubmodule.subtype
    Subtype.val_injective
  letI : FiniteDimensional k (center k 𝔤) := FiniteDimensional.of_injective
    (center k 𝔤).toSubmodule.subtype Subtype.val_injective
  letI : IsLieAbelian C := LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra k S C
  let B := finBasis k C
  let Z := center k 𝔤
  let BZ := finBasis k Z
  let embC : C →ₗ[k] 𝔤 := S.toSubmodule.subtype.comp C.toSubmodule.subtype
  let embZ : Z →ₗ[k] 𝔤 := Z.toSubmodule.subtype
  have hComm (x y : C) (z w : Z) :
      ⁅cartanCenterDirection C x z, cartanCenterDirection C y w⁆ = 0 := by
    unfold cartanCenterDirection
    rw [lie_add_center_add_center (L := 𝔤) _ _ z w]
    exact congrArg (fun x : C => ((x : S) : 𝔤)) (trivial_lie_zero C C x y)
  have hSemi (x : C) (z : Z) : Module.End.IsSemisimple
      (Matrix.toLinAlgEquiv' (hopfLieMatrix U.val (cartanCenterDirection C x z))) := by
    have hs : (ad k S (x : S)).IsSemisimple :=
      LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra
        (K := k) (L := S) (H := C) (x := x.val) x.property
    exact hopfLieMatrix_isSemisimple_of_ad_isSemisimple U hΔ hε hGen hZ
      (cartanCenterDirection C x z) (ad_add_center_isSemisimple S hC (x : S) z hs)
  let I := Fin (finrank k C) ⊕ Fin (finrank k Z)
  let a : I → C := Sum.elim B fun _ => 0
  let z : I → Z := Sum.elim (fun _ => 0) BZ
  let D (r : I) := cartanCenterDirection C (a r) (z r)
  obtain ⟨P, d, f, hf, hDiag, hLift⟩ :=
    exists_diagonalTorus_of_commuting_semisimple_tangents U hΔ hε hGen D
      (fun r s => hComm (a r) (a s) (z r) (z s)) (fun r => hSemi (a r) (z r))
  letI : NoZeroSMulDivisors ℤ k := NoZeroSMulDivisors.int_of_charZero k k
  refine ⟨_, _, P, d, f, hf, hDiag, ?_, diagonalWeightLattice_exists_basis d⟩
  intro x y
  classical
  choose v hv using hLift
  let L := (hopfInvariantDerivationsMap f).toLinearMap
  have hv₁ (i : Fin (finrank k C)) : L (v (.inl i)) = embC (B i) := by
    change hopfInvariantDerivationsMap f (v (.inl i)) = _
    rw [hv]
    simp only [D, a, z, Sum.elim_inl, cartanCenterDirection, ZeroMemClass.coe_zero, add_zero, embC,
      LinearMap.comp_apply, Submodule.subtype_apply]
    rfl
  have hv₂ (i : Fin (finrank k Z)) : L (v (.inr i)) = embZ (BZ i) := by
    change hopfInvariantDerivationsMap f (v (.inr i)) = _
    rw [hv]
    simp only [D, a, z, Sum.elim_inr, cartanCenterDirection, ZeroMemClass.coe_zero, zero_add, embZ,
      Submodule.subtype_apply]
    rfl
  have hX : embC x ∈ LinearMap.range L := by
    rw [← B.sum_repr x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact Submodule.smul_mem _ _ ⟨v (.inl i), hv₁ i⟩
  have hY : embZ y ∈ LinearMap.range L := by
    rw [← BZ.sum_repr y, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact Submodule.smul_mem _ _ ⟨v (.inr i), hv₂ i⟩
  exact Submodule.add_mem (LinearMap.range L) hX hY

end Torus

end WideE
