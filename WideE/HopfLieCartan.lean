import WideE.CartanCriterion
import WideE.HopfLieJordan

/-! For an algebraic matrix Lie algebra with no nilpotent center, adjoint
semisimplicity implies semisimplicity in the generating representation. -/

noncomputable section

open scoped Matrix TensorProduct
open LieAlgebra LieModule Module Module.End

namespace WideE

attribute [local instance] LieRing.ofAssociativeRing

section Eigenvectors

variable {k L V : Type*} [Field k] [CharZero k] [IsAlgClosed k] [LieRing L] [LieAlgebra k L]
  [FiniteDimensional k L] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private theorem nilpotentPart_mem_center_of_semisimple_ad
    (ρ : L →ₗ⁅k⁆ End k V) (hρ : Function.Injective ρ) {x s n : L}
    (hx : x = s + n) (hxAd : (ad k L x).IsSemisimple) (hs : (ρ s).IsSemisimple)
    (hn : IsNilpotent (ρ n)) (hComm : ⁅s, n⁆ = 0) : n ∈ center k L := by
  have hρComm : Commute (ρ s) (ρ n) := by
    rw [commute_iff_lie_eq, ← LieHom.map_lie, hComm, LieHom.map_zero]
  have hPoly := ad_nilpotent_mem_adjoin_of_jordan hρComm hs hn
  rw [← LieHom.map_add, ← hx, Algebra.adjoin_singleton_eq_range_aeval] at hPoly
  obtain ⟨p, hp⟩ := hPoly
  change Polynomial.aeval (ad k (End k V) (ρ x)) p = ad k (End k V) (ρ n) at hp
  obtain ⟨b, d, hb⟩ := exists_eigenbasis_of_isSemisimple (ad k L x) hxAd
  have hNil : IsNilpotent (ad k (End k V) (ρ n)) := ad_nilpotent_of_nilpotent k hn
  have hAd : ad k L n = 0 := by
    apply b.ext
    intro i
    have hNe : ρ (b i) ≠ 0 := fun h => b.ne_zero i (hρ (h.trans ρ.map_zero.symm))
    have hEig : (ad k (End k V) (ρ x)).HasEigenvector (d i) (ρ (b i)) := by
      refine ⟨mem_eigenspace_iff.mpr ?_, hNe⟩
      rw [ad_apply, ← LieHom.map_lie, ← ad_apply k L, hb, LieHom.map_smul]
    have hVal := aeval_apply_of_hasEigenvector (p := p) hEig
    rw [hp] at hVal
    have hEval : (ad k (End k V) (ρ n)).HasEigenvalue (p.eval (d i)) :=
      hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hVal, hNe⟩
    have hd : p.eval (d i) = 0 := (hEval.isNilpotent_of_isNilpotent hNil).eq_zero
    apply hρ
    rw [hd, zero_smul] at hVal
    rw [LinearMap.zero_apply, LieHom.map_zero, ad_apply, LieHom.map_lie, ← ad_apply k]
    exact hVal
  apply (mem_maxTrivSubmodule k L L _).mpr
  intro y
  rw [← lie_skew, ← ad_apply k L, hAd, LinearMap.zero_apply, neg_zero]

end Eigenvectors

section Cartan

variable {k H ι : Type*} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι] [Algebra.FiniteType k H]

/-- An adjoint-semisimple Lie vector is semisimple on a generating matrix
representation if the center has no nonzero nilpotent tangent matrix. -/
theorem hopfLieMatrix_isSemisimple_of_ad_isSemisimple (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (hZ : ∀ x ∈ center k (hopfInvariantDerivations k H), IsNilpotent (hopfLieMatrix U.val x) → x = 0)
    (x : hopfInvariantDerivations k H) (hx : (ad k _ x).IsSemisimple) :
    Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (hopfLieMatrix U.val x)) := by
  letI := hopfCotangent_finiteDimensional k H
  letI : FiniteDimensional k (hopfInvariantDerivations k H) :=
    FiniteDimensional.of_surjective (hopfLieVectorInvariantDerivations (k := k) (H := H)).toLinearMap
      (hopfLieVectorInvariantDerivations (k := k) (H := H)).surjective
  obtain ⟨s, n, he, hs, hn, hComm⟩ := exists_hopfLieMatrix_jordanDecomposition U hΔ hε hGen x
  let E : Matrix ι ι k ≃ₐ[k] End k (ι → k) := Matrix.toLinAlgEquiv'
  let ρ := E.toLieEquiv.toLieHom.comp (hopfLieMatrixHom U.val hΔ)
  have hρ : Function.Injective ρ := E.injective.comp (hopfLieMatrixHom_injective U.val hΔ hGen)
  have hz := nilpotentPart_mem_center_of_semisimple_ad ρ hρ he hx hs (hn.map E.toAlgHom) hComm
  rw [hZ n hz hn, add_zero] at he
  rw [he]
  exact hs

end Cartan

end WideE
