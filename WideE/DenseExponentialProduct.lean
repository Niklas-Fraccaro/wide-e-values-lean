import WideE.BigCellCentralizer
import WideE.HopfDominance
import WideE.HopfPolynomialTangent
import WideE.HopfProductDerivative
import WideE.AdjointCentralizerTangent
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import MixedRelativeTensorDerivation

/-! An actual affine chart of exponential and torus factors. A spanning
family of their Lie directions makes the ordered product dominant. -/

noncomputable section

open scoped TensorProduct Matrix Polynomial

namespace WideE

section Parameters

variable {k H Q ν : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing Q] [HopfAlgebra k Q]

local notation "P" => MvPolynomial ν k
local notation "A" => Q ⊗[k] P
local notation "εQ" => Bialgebra.counitAlgHom k Q
local notation "εH" => Bialgebra.counitAlgHom k H

private def exponentialParameter (j : ν) : A :=
  (1 : Q) ⊗ₜ[k] (MvPolynomial.X j : P)

private def productIdentityPoint : A →ₐ[k] k :=
  tensorPoint (εQ) (MvPolynomial.aeval (0 : ν → k))

private def productParameterDerivation (z : HopfLieVector k Q k) (d : ν → k) : Derivation k A A :=
  StrictEUnit.mixedRelativeTensorDerivation (0 : Derivation k k k)
    (hopfLieVectorInvariantDerivations z).val
    (MvPolynomial.mkDerivation k (fun i => MvPolynomial.C (d i))) (by simp) (by simp)

private theorem productIdentityPoint_param (j : ν) :
    productIdentityPoint (exponentialParameter (Q := Q) (k := k) j) = 0 := by
  simp only [productIdentityPoint, exponentialParameter, tensorPoint_tmul, map_one, one_mul,
    MvPolynomial.aeval_X, Pi.zero_apply]

private theorem productIdentityPoint_aeval (j : ν) :
    (productIdentityPoint (Q := Q) (k := k)).comp
      (Polynomial.aeval (exponentialParameter (Q := Q) (k := k) j)) = Polynomial.aeval (0 : k) := by
  apply Polynomial.algHom_ext
  rw [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.aeval_X, productIdentityPoint_param]

private theorem productParameterDerivation_param (z : HopfLieVector k Q k) (d : ν → k) (j : ν) :
    productIdentityPoint (productParameterDerivation z d (exponentialParameter j)) = d j := by
  simp only [productParameterDerivation, productIdentityPoint, exponentialParameter,
    StrictEUnit.mixedRelativeTensorDerivation_tmul, Derivation.map_one_eq_zero,
    TensorProduct.zero_tmul, zero_add, MvPolynomial.mkDerivation_X, tensorPoint_tmul, map_one,
    one_mul, MvPolynomial.aeval_C, Algebra.id.map_eq_id, RingHom.id_apply]

private def addExponentialParameter (j : ν) (p : H →ₐ[k] k[X]) : H →ₐ[k] A :=
  (Polynomial.aeval (exponentialParameter j)).comp p

private theorem addExponentialParameter_eval (j : ν) (p : H →ₐ[k] k[X])
    (hp : (Polynomial.aeval (0 : k)).comp p = εH) :
    productIdentityPoint.comp (addExponentialParameter (Q := Q) j p) = εH := by
  rw [addExponentialParameter, ← AlgHom.comp_assoc, productIdentityPoint_aeval, hp]

private theorem addExponentialParameter_derivative
    (j : ν) (p : H →ₐ[k] k[X]) (x : HopfLieVector k H k)
    (hp : ∀ a, Polynomial.aeval (0 : k) (Polynomial.derivative (p a)) =
      x (hopfCotangentProjection k H a))
    (z : HopfLieVector k Q k) (d : ν → k) (a : H) :
    productIdentityPoint (productParameterDerivation z d (addExponentialParameter j p a)) =
      d j * x (hopfCotangentProjection k H a) := by
  rw [addExponentialParameter, AlgHom.comp_apply, Derivation.map_aeval, Algebra.id.smul_eq_mul, map_mul,
    productParameterDerivation_param, ← AlgHom.comp_apply, productIdentityPoint_aeval, hp, mul_comm]

private theorem productIdentityPoint_torus (π : H →ₐc[k] Q) :
    (productIdentityPoint (ν := ν)).comp
      ((Algebra.TensorProduct.includeLeft : Q →ₐ[k] A).comp (π : H →ₐ[k] Q)) = εH := by
  apply AlgHom.ext
  intro a
  change tensorPoint (εQ) (MvPolynomial.aeval (0 : ν → k)) (π a ⊗ₜ[k] (1 : P)) = _
  rw [tensorPoint_tmul, map_one, mul_one]
  exact CoalgHomClass.counit_comp_apply π a

private theorem productParameterDerivation_torus (π : H →ₐc[k] Q)
    (z : HopfLieVector k Q k) (d : ν → k) (a : H) :
    productIdentityPoint (productParameterDerivation z d ((π a) ⊗ₜ[k] (1 : P))) =
      z (hopfCotangentProjection k Q (π a)) := by
  simp only [productParameterDerivation, productIdentityPoint,
    StrictEUnit.mixedRelativeTensorDerivation_tmul, Derivation.map_one_eq_zero,
    TensorProduct.tmul_zero, add_zero, tensorPoint_tmul, map_one, mul_one,
    hopfLieVectorInvariantDerivations_counit]

end Parameters

section ProductMatrices

variable {k H A ι β : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A] [Fintype ι] [DecidableEq ι] [LinearOrder β]

private theorem hopfPointListProduct_blockUnitriangular
    (w : ι → β) (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (l : List (H →ₐ[k] A)) (hl : ∀ p ∈ l, BlockUnitriangular w (U.val.map p)) :
    BlockUnitriangular w (U.val.map (hopfPointListProduct l)) := by
  letI : Group (H →ₐ[k] A) := hopfPointGroup
  let ρ := hopfPointMatrix (A := A) U hΔ hε
  induction l with
  | nil =>
    change BlockUnitriangular w (ρ 1).val
    rw [map_one]
    exact BlockUnitriangular.one w
  | cons p l ih =>
    change BlockUnitriangular w (ρ (p * hopfPointListProduct l)).val
    rw [map_mul]
    exact (hl p List.mem_cons_self).mul (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)))

end ProductMatrices

section DenseProduct

variable {k H Q ι β σ τ : Type*} [Field k] [CharZero k]
  [CommRing H] [HopfAlgebra k H] [IsDomain H] [Algebra.FiniteType k H]
  [CommRing Q] [HopfAlgebra k Q] [IsDomain Q]
  [Fintype ι] [DecidableEq ι] [LinearOrder β] [Fintype σ] [Fintype τ]

local notation "A" => Q ⊗[k] MvPolynomial (σ ⊕ τ) k
local notation "εH" => Bialgebra.counitAlgHom k H
local notation "C" => HopfCotangent k H
local notation "𝔤" => HopfLieVector k H k
local notation "𝔱" => HopfLieVector k Q k

set_option maxHeartbeats 1800000 in
/-- A torus and strictly triangular exponential directions spanning the Lie
algebra give a dense lower, torus, upper product in the actual group. -/
theorem exists_dense_blockProduct_of_exponentials
    (w : ι → β) (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (π : H →ₐc[k] Q) (xLower : σ → 𝔤) (xUpper : τ → 𝔤)
    (hLower : ∀ r i j, ¬w j < w i → hopfCotangentMatrix U.val (xLower r) i j = 0)
    (hUpper : ∀ r i j, ¬w i < w j → hopfCotangentMatrix U.val (xUpper r) i j = 0)
    (hSpan : Function.Surjective fun z : 𝔱 × ((σ ⊕ τ) → k) =>
      hopfLiePullback (π : H →ₐ[k] Q) (BialgHomClass.counitAlgHom_comp π) z.1 +
        ∑ j, z.2 j • Sum.elim xLower xUpper j) :
    ∃ (f : H →ₐ[k] A) (Mlower Mupper : (Matrix ι ι A)ˣ),
      Function.Injective f ∧
      BlockUnitriangular (OrderDual.toDual ∘ w) Mlower.val ∧ BlockUnitriangular w Mupper.val ∧
      U.val.map f = Mlower.val * U.val.map ((Algebra.TensorProduct.includeLeft : Q →ₐ[k] A).comp
        (π : H →ₐ[k] Q)) * Mupper.val := by
  classical
  let wLower := OrderDual.toDual ∘ w
  choose pLower hPLower hQLower hDLower using fun r =>
    exists_hopfPolynomialPoint_of_strictBlocks wLower U hΔ hε hGen (xLower r) (hLower r)
  choose pUpper hPUpper hQUpper hDUpper using fun r =>
    exists_hopfPolynomialPoint_of_strictBlocks w U hΔ hε hGen (xUpper r) (hUpper r)
  let fLower (r : σ) : H →ₐ[k] A := addExponentialParameter (Sum.inl r) (pLower r)
  let fUpper (r : τ) : H →ₐ[k] A := addExponentialParameter (Sum.inr r) (pUpper r)
  let q : A →ₐ[k] k := productIdentityPoint
  let pT := (Algebra.TensorProduct.includeLeft : Q →ₐ[k] A).comp (π : H →ₐ[k] Q)
  let l := (Finset.univ : Finset σ).toList.map fLower
  let u := (Finset.univ : Finset τ).toList.map fUpper
  let f := hopfPointListProduct (l ++ pT :: u)
  letI : Group (H →ₐ[k] A) := hopfPointGroup
  let ρ : (H →ₐ[k] A) →* (Matrix ι ι A)ˣ := hopfPointMatrix U hΔ hε
  let Mlower := ρ (hopfPointListProduct l)
  let Mupper := ρ (hopfPointListProduct u)
  have hlP : ∀ p ∈ l, BlockUnitriangular wLower (U.val.map p) := by
    intro p hp
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
    exact (hPLower r).map (Polynomial.aeval (R := k) (exponentialParameter (Q := Q) (k := k) (Sum.inl r : σ ⊕ τ))).toRingHom
  have huP : ∀ p ∈ u, BlockUnitriangular w (U.val.map p) := by
    intro p hp
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
    exact (hPUpper r).map (Polynomial.aeval (R := k) (exponentialParameter (Q := Q) (k := k) (Sum.inr r : σ ⊕ τ))).toRingHom
  have hProd : U.val.map f = Mlower.val * U.val.map pT * Mupper.val := by
    change (ρ f).val = (Mlower * ρ pT * Mupper).val
    apply congrArg Units.val
    change ρ (hopfPointListProduct (l ++ pT :: u)) = _
    rw [hopfPointListProduct_append, hopfPointListProduct_cons]
    change ρ (hopfPointListProduct l * (pT * hopfPointListProduct u)) = _
    rw [map_mul, map_mul, mul_assoc]
  refine ⟨f, Mlower, Mupper, ?_,
    hopfPointListProduct_blockUnitriangular wLower U hΔ hε l hlP,
    hopfPointListProduct_blockUnitriangular w U hΔ hε u huP, hProd⟩
  have hqAll : ∀ p ∈ l ++ pT :: u, q.comp p = εH := by
    intro p hp
    rcases List.mem_append.mp hp with hl | hu
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
      exact addExponentialParameter_eval (Sum.inl j) (pLower j) (hQLower j)
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact productIdentityPoint_torus π
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hu
        exact addExponentialParameter_eval (Sum.inr j) (pUpper j) (hQUpper j)
  have hqBase : q.comp f = εH := hopfPointListProduct_at_identity q _ hqAll
  have hDerivative (z : 𝔱) (d : (σ ⊕ τ) → k) (a : H) :
      q (productParameterDerivation z d (f a)) =
        (hopfLiePullback (π : H →ₐ[k] Q) (BialgHomClass.counitAlgHom_comp π) z +
          ∑ j, d j • Sum.elim xLower xUpper j) (hopfCotangentProjection k H a) := by
    change q (productParameterDerivation z d (hopfPointListProduct (l ++ pT :: u) a)) = _
    rw [derivative_hopfPointListProduct_at_identity _ q _ hqAll]
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, l, u,
      List.map_map, Finset.sum_map_toList]
    have hT : q (productParameterDerivation z d (pT a)) =
        z (hopfCotangentProjection k Q (π a)) :=
      productParameterDerivation_torus π z d a
    have hL (r : σ) : q (productParameterDerivation z d (fLower r a)) =
        d (Sum.inl r) * xLower r (hopfCotangentProjection k H a) :=
      addExponentialParameter_derivative (Sum.inl r) (pLower r) (xLower r) (hDLower r) z d a
    have hU (r : τ) : q (productParameterDerivation z d (fUpper r a)) =
        d (Sum.inr r) * xUpper r (hopfCotangentProjection k H a) :=
      addExponentialParameter_derivative (Sum.inr r) (pUpper r) (xUpper r) (hDUpper r) z d a
    simp only [Function.comp_apply, hL, hU, hT,
      LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hopfLiePullback_projection,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact add_left_comm _ _ _
  letI : IsDomain A := Equiv.isDomain
    (MvPolynomial.algebraTensorAlgEquiv k Q (σ := σ ⊕ τ)).toRingEquiv
  letI := hopfCotangent_finiteDimensional k H
  let b := Module.finBasis k C
  choose s hs using fun i => hopfCotangentProjection_surjective k H (b i)
  choose d hd using fun i => hSpan (b.coord i)
  let D (r : Fin (Module.finrank k C)) := productParameterDerivation (d r).1 (d r).2
  have hJ : (Matrix.of fun r i => q (D r (f (s i)))).det ≠ 0 := by
    have hEq : Matrix.of (fun r i => q (D r (f (s i)))) = 1 := by
      apply Matrix.ext
      intro r i
      change q (productParameterDerivation (d r).1 (d r).2 (f (s i))) = _
      have hSel : hopfLiePullback (π : H →ₐ[k] Q) (BialgHomClass.counitAlgHom_comp π) (d r).1 +
          ∑ j, (d r).2 j • Sum.elim xLower xUpper j = b.coord r := hd r
      rw [hDerivative, hSel, hs]
      simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, Matrix.one_apply, eq_comm]
    rw [hEq, Matrix.det_one]
    exact one_ne_zero
  exact injective_hopfMap_of_tangent_jacobian b f q hqBase s hs D hJ

end DenseProduct

end WideE
