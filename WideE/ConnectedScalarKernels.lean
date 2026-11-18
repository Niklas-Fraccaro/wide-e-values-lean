import WideE.ConnectedMultiplicativeKernel
import WideE.GrouplikeRoot
import WideE.RegularKernelTorsor
import WideE.ScalarHopfIdeal
import WideE.ScalarKernelConnected
import WideE.UpperTriangularScalar

/-! Connected scalar kernels for finite-type affine groups over the algebraic numbers. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section

local notation "K" => AlgebraicComplex
local notation "P" => Polynomial K
local notation "L" => LaurentPolynomial K

variable {H : Type} [CommRing H] [IsDomain H] [HopfAlgebra K H] [Algebra.FiniteType K H]

attribute [local instance] additivePolynomialHopf

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The actual principal kernel of a nonzero primitive coordinate has an integral coordinate ring. -/
theorem primitiveIdeal_quotient_isDomain (x : H) (hx : x ≠ 0)
    (hε : Coalgebra.counit (R := K) x = 0)
    (hΔ : Coalgebra.comul (R := K) x = (1 : H) ⊗ₜ[K] x + x ⊗ₜ[K] (1 : H)) :
    IsDomain (H ⧸ Ideal.span {x}) := by
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  let j := additiveScalarMap x hε hΔ
  have hjX : j Polynomial.X = x := additiveScalarMap_X x hε hΔ
  let I : Ideal H := Ideal.span {x}
  let hI : IsHopfIdeal K I := primitiveIdeal_isHopf x (by simpa only [add_comm] using hΔ) hε
  letI := hI.quotientHopf
  let π := hI.quotientBialgHom
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (π : H →ₐ[K] H ⧸ I).toRingHom = Ideal.span {j Polynomial.X} := by
    rw [hjX]
    exact Ideal.mk_ker
  have hj := additiveGroupQuotient_faithfullyFlat j
    (additiveGroupQuotient_injective j (show j Polynomial.X ≠ 0 by rw [hjX]; exact hx))
  let f : P →ₐ[K] H := j
  letI : Algebra P H := f.toRingHom.toAlgebra
  letI : IsScalarTower K P H := IsScalarTower.of_algHom f
  letI : CharZero P := Algebra.charZero_of_charZero K P
  let T := additiveRelativeKernelTorsor j π hπ hker hj
  letI : ConnectedSpace (PrimeSpectrum (H ⧸ I)) := affineLineTorsor_group_connected T
  exact T.group_isDomain_of_integral_total

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxHeartbeats 150000 in
/-- A nontrivial group-like coordinate has a group-like root with counit one
and an integral principal kernel. -/
theorem exists_grouplikeRoot_domainKernel (x : Hˣ) (hx : (x : H) ≠ 1)
    (hε : Coalgebra.counit (R := K) (x : H) = 1)
    (hΔ : Coalgebra.comul (R := K) (x : H) = (x : H) ⊗ₜ[K] (x : H)) :
    ∃ (d : ℕ) (u : Hˣ), 0 < d ∧ (u : H) ^ d = (x : H) ∧ (u : H) ≠ 1 ∧
      Coalgebra.counit (R := K) (u : H) = 1 ∧
      Coalgebra.comul (R := K) (u : H) = (u : H) ⊗ₜ[K] (u : H) ∧
      IsDomain (H ⧸ Ideal.span {(u : H) - 1}) := by
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  let j := multiplicativeScalarMap x hε hΔ
  have hjT : j (LaurentPolynomial.T 1) = x := multiplicativeScalarMap_T x hε hΔ
  let I : Ideal H := Ideal.span {(x : H) - 1}
  let hI : IsHopfIdeal K I := grouplikeIdeal_isHopf (x : H) hΔ hε
  letI := hI.quotientHopf
  let π := hI.quotientBialgHom
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (π : H →ₐ[K] H ⧸ I).toRingHom =
      Ideal.span {j (LaurentPolynomial.T 1) - 1} := by
    rw [hjT]
    exact Ideal.mk_ker
  have hj := multiplicativeGroupQuotient_faithfullyFlat j
    (multiplicativeGroupQuotient_injective j (show j (LaurentPolynomial.T 1) ≠ 1 by rw [hjT]; exact hx))
  let f : L →ₐ[K] H := j
  letI : Algebra L H := f.toRingHom.toAlgebra
  letI : IsScalarTower K L H := IsScalarTower.of_algHom f
  let T := multiplicativeRelativeKernelTorsor j π hπ hker hj
  let p := Bialgebra.counitAlgHom K H
  have hp : p (algebraMap L H (LaurentPolynomial.T 1)) = 1 := by
    change p (j (LaurentPolynomial.T 1)) = 1
    rw [hjT]
    exact hε
  obtain ⟨d, u, hd, hpow, huε, hconn, hred⟩ :=
    laurentTorsor_exists_normalizedRoot_reducedConnectedFiber T p hp
  have hpow' : (u : H) ^ d = (x : H) := hpow.trans hjT
  have hu : (u : H) ≠ 1 := by
    intro h
    rw [h, one_pow] at hpow'
    exact hx hpow'.symm
  have huΔ := grouplike_of_power_grouplike u huε hd (by rw [hpow']; exact hΔ)
  let Iu : Ideal H := Ideal.span {(u : H) - 1}
  let Ju := H ⧸ Iu
  let hIu : IsHopfIdeal K Iu := grouplikeIdeal_isHopf (u : H) huΔ huε
  letI := hIu.quotientHopf
  letI : Algebra.FiniteType K Ju := Algebra.FiniteType.of_surjective inferInstance
    (Ideal.Quotient.mkₐ K Iu) (Ideal.Quotient.mkₐ_surjective K Iu)
  letI : ConnectedSpace (PrimeSpectrum Ju) := hconn
  letI : IsReduced Ju := hred
  exact ⟨d, u, hd, hpow', hu, huε, huΔ, hopfDomain_of_connected_reduced (k := K) (H := Ju)⟩

end

end WideE
