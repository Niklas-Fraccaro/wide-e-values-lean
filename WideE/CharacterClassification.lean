import WideE.Classification
import WideE.FiberUnitCharacter
import WideE.HopfConnectedDomain
import WideE.KummerWeightDescent
import WideE.MatrixOrbitWeights
import WideE.PointedKummer
import WideE.PVFirstBlock
import WideE.PVOrbit
import WideE.ResidualConnectedReduction
import WideE.WideFiberInjectivity

/-! The inverse pair lifts by its character on the connected torsor. -/

open scoped WideE TensorProduct Matrix Kronecker

noncomputable section

namespace WideE

local notation "Coefficients" => AlgebraicComplex
local notation "R" => LaurentPolynomial AlgebraicComplex
local notation "D" => widePuncturedDerivation

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule Subalgebra.toCommRing

set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 120000

private def restrictTensorScalars {k B S H : Type*}
    [CommRing k] [CommRing B] [CommRing S] [CommRing H]
    [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [Algebra k H]
    (ρ : S →ₐ[B] S ⊗[k] H) : S →ₐ[k] S ⊗[k] H :=
  ρ.restrictScalars k

set_option maxHeartbeats 6000000 in
/-- An inverse relation in the fiber gives Laurent coordinates after a pointed
Kummer pullback. Only the two opposite character weights are descended. -/
theorem exists_kummer_inverse_coordinates
    (M : Submodule R WidePunctured) (hM : ∀ x ∈ M, D x ∈ M) (h₁ : (1 : WidePunctured) ∈ M)
    {m n : ℕ} (bM : Basis (Fin m) R M) (bN : Basis (Fin n) R (M * M : Submodule R WidePunctured))
    (f g h : M) (hfg : f.val * g.val - 1 = (LaurentPolynomial.T 1 - 1 : R) • h.val) :
    ∃ (q : ℕ), 0 < q ∧ ∃ X Y : Fin m → R,
      (∀ i, evalAtOne Coefficients (X i) = evalAtOne Coefficients (bM.repr f i)) ∧
      (∀ i, evalAtOne Coefficients (Y i) = evalAtOne Coefficients (bM.repr g i)) ∧
      coordinateProduct (fun i j l => kummer Coefficients q (bN.repr (productBilinear M (bM i) (bM j)) l))
        X Y = fun l => kummer Coefficients q (bN.repr (productOne M h₁) l) := by
  classical
  let δ := (laurentDerivation (K := Coefficients)).toLinearMap.toAddMonoidHom
  let d := (D).toLinearMap.toAddMonoidHom
  let N : Submodule R WidePunctured := M * M
  have hLeib (x y : WidePunctured) : d (x * y) = d x * y + x * d y := widePuncturedDerivation_mul x y
  have hD (p : R) (x : WidePunctured) : d (p • x) = δ p • x + p • d x := widePuncturedDerivation_smul p x
  have hN : ∀ x ∈ N, d x ∈ N := productModule_stable d hM hLeib
  let DM := restrictConnection d M hM
  let DN := restrictConnection d N hN
  let BM := connectionSystemMatrix bM DM
  let BN := connectionSystemMatrix bN DN
  let F := productCoefficientMatrix bM bN (productBilinear M)
  let u : Fin n → R := bN.repr (productOne M h₁)
  have hF : F.map laurentDerivation = BN * F - F *
      (BM ⊗ₖ (1 : Matrix (Fin m) (Fin m) R) + (1 : Matrix (Fin m) (Fin m) R) ⊗ₖ BM) :=
    productCoefficientMatrix_horizontal bM bN δ DM DN (productBilinear M)
      (restrictConnection_smul d N hN δ hD) (productBilinear_restrictConnection d M hM hLeib)
  have hU : laurentDerivation ∘ u = BN *ᵥ u :=
    repr_horizontal_unit bN δ DN (restrictConnection_smul d N hN δ hD)
      (productOne_restrictConnection d M hM hLeib h₁ (D).map_one_eq_zero)
  let A := combinedLaurentSystem BM BN
  let S := ordinaryPVAlgebra A
  letI : CommRing S := (ordinaryPVAlgebra A).toCommRing
  letI : Algebra R S := (ordinaryPVAlgebra A).algebra
  letI : Algebra Coefficients S := (ordinaryPVAlgebra A).algebra'
  letI : IsAlgClosed Coefficients := IsAlgClosure.isAlgClosed ℚ
  letI := ordinaryPVHopf A
  let T := ordinaryPVTorsor A
  letI : Algebra.FiniteType Coefficients (ordinaryPVGroup A) := T.group_finiteType
  let p := ordinaryPVAtOne A
  obtain ⟨G⟩ := ordinaryPV_componentHopf A
  let Q := componentTorsorQuotient T G
  letI : CommRing Q := Q.toCommRing
  letI : Algebra R Q := Q.algebra
  letI : Algebra Coefficients Q := Q.algebra'
  letI : Algebra Q S := Q.toAlgebra
  letI : SMul Coefficients Q := Algebra.toSMul
  letI : SMul Coefficients S := Algebra.toSMul
  letI : SMul Q S := Algebra.toSMul
  letI : SMul R Q := Algebra.toSMul
  letI : SMul R S := Algebra.toSMul
  letI : IsScalarTower Coefficients Q S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower Coefficients R Q := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply Coefficients R S a
  letI : IsScalarTower R Q S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI := G.identityHopf
  letI := ordinaryPVIdentityComponent_isDomain A G
  let H := G.IdentityComponent
  let ρ := ordinaryPVRestrictedCoaction A G.identityQuotient
  let o := ordinaryPVOrbit A G.identityQuotient
  let T₀ := identityComponentTorsor T G
  let cmp := coordinateComparison_of_ordinaryPV BM BN hF hU
  let U := ordinaryPVFirstBlock BM BN
  have hUeq : cmp.onM.val = U := coordinateComparison_of_ordinaryPV_onM BM BN hF hU
  let x₀ : Fin m → Coefficients := evalAtOne Coefficients ∘ bM.repr f
  let y₀ : Fin m → Coefficients := evalAtOne Coefficients ∘ bM.repr g
  let x := U *ᵥ (algebraMap Coefficients S ∘ x₀)
  let y := U *ᵥ (algebraMap Coefficients S ∘ y₀)
  let base := algebraMap R S
  let c (i j : Fin m) (l : Fin n) := F l (i, j)
  let eval := evalAtOne Coefficients
  have hScalar (a : Coefficients) : base (LaurentPolynomial.C a) = algebraMap Coefficients S a :=
    (IsScalarTower.algebraMap_apply Coefficients R S a).symm
  have hRel := inverse_coordinates_of_factorization M h₁ bM bN f g h hfg
  have hRelS : coordinateProduct (fun i j l => base (LaurentPolynomial.C (eval (c i j l))))
      (algebraMap Coefficients S ∘ x₀) (algebraMap Coefficients S ∘ y₀) =
        fun l => base (LaurentPolynomial.C (eval (u l))) := by
    funext l
    have he := map_coordinateProduct (algebraMap Coefficients S) (fun i j l => eval (c i j l)) x₀ y₀ l
    change coordinateProduct (fun i j l => eval (c i j l)) x₀ y₀ = eval ∘ u at hRel
    rw [hRel] at he
    change algebraMap Coefficients S (eval (u l)) =
      coordinateProduct (fun i j l' => algebraMap Coefficients S (eval (c i j l')))
        (algebraMap Coefficients S ∘ x₀) (algebraMap Coefficients S ∘ y₀) l at he
    simpa only [hScalar, Function.comp_apply] using he.symm
  have hProdS : coordinateProduct (fun i j l => base (c i j l)) x y = base ∘ u := by
    have hh := cmp.transportInverse hRelS
    rw [hUeq] at hh
    exact hh
  have hOrbitBase (r : R) : o (base r) = algebraMap Coefficients H (eval r) :=
    ordinaryPVOrbit_algebraMap A G.identityQuotient r
  have hProdH : coordinateProduct (fun i j l => algebraMap Coefficients H (eval (c i j l)))
      (o ∘ x) (o ∘ y) = (algebraMap Coefficients H) ∘ eval ∘ u := by
    funext l
    have hh := (map_coordinateProduct o.toRingHom (fun i j l => base (c i j l)) x y l).symm.trans
      (congrArg o.toRingHom (congrFun hProdS l))
    change coordinateProduct (fun i j l' => o (base (c i j l'))) (o ∘ x) (o ∘ y) l =
      o (base (u l)) at hh
    simpa only [hOrbitBase, Function.comp_apply] using hh
  let a (i : Fin m) := puncturedEvaluation 1 (bM i : WidePunctured)
  let b (l : Fin n) := puncturedEvaluation 1 (bN l : WidePunctured)
  have hProd (i j : Fin m) : a i * a j = ∑ l, eval (c i j l) • b l := by
    have hh := puncturedEvaluation_eq_sum_repr bN (productBilinear M (bM i) (bM j))
    change puncturedEvaluation 1 ((bM i : WidePunctured) * (bM j : WidePunctured)) = _ at hh
    rw [map_mul] at hh
    exact hh
  have hOne : ∑ l, eval (u l) • b l = 1 := by
    have hh := puncturedEvaluation_eq_sum_repr bN (productOne M h₁)
    change puncturedEvaluation 1 1 = _ at hh
    rw [map_one] at hh
    exact hh.symm
  have hUV := inverse_tensor_of_coordinateProduct a b (fun i j l => eval (c i j l)) (eval ∘ u)
    hProd hOne (o ∘ x) (o ∘ y) hProdH
  have hπ (v : ordinaryPVGroup A) : Bialgebra.counitAlgHom Coefficients H (G.identityQuotient v) =
      Bialgebra.counitAlgHom Coefficients (ordinaryPVGroup A) v :=
    DFunLike.congr_fun G.identityCounit_comp_quotient v
  have hSpec (z₀ : Fin m → Coefficients) (i : Fin m) :
      p ((U *ᵥ (algebraMap Coefficients S ∘ z₀)) i) = z₀ i := by
    let p' := p.restrictScalars Coefficients
    have hn : U.map p' = 1 := ordinaryPVFirstBlock_atOne BM BN
    have hs (z : Coefficients) : p' (algebraMap Coefficients S z) = z := p'.commutes z
    change p'.toRingHom ((U *ᵥ (algebraMap Coefficients S ∘ z₀)) i) = z₀ i
    rw [RingHom.map_mulVec, show U.map p'.toRingHom = 1 from hn, Matrix.one_mulVec]
    exact hs _
  have hXε (i : Fin m) : Bialgebra.counitAlgHom Coefficients H ((o ∘ x) i) = x₀ i :=
    (ordinaryPVOrbit_counit A G.identityQuotient hπ (x i)).trans (hSpec x₀ i)
  have hYε (i : Fin m) : Bialgebra.counitAlgHom Coefficients H ((o ∘ y) i) = y₀ i :=
    (ordinaryPVOrbit_counit A G.identityQuotient hπ (y i)).trans (hSpec y₀ i)
  obtain ⟨χ, hχ, hX, hY⟩ := inverse_tensor_coordinates_have_character a
    (linearIndependent_wideBasisValues hM bM) x₀ y₀ (o ∘ x) (o ∘ y) hXε hYε hUV
  have hρ := ordinaryPVFirstBlock_coaction BM BN G.identityQuotient
  let ρk := restrictTensorScalars (k := Coefficients) ρ
  have hx := weighted_vector_of_matrix_orbit ρk o U hρ x₀ (χ : H) hX
  have hy := weighted_vector_of_matrix_orbit ρk o U hρ y₀ (↑χ⁻¹ : H) hY
  obtain ⟨q, hq, j, hj⟩ := exists_pointed_kummerComponentMap_of_cover
    finiteLaurentCoverHasPointedKummerMap_algebraicComplex T G (p.restrictScalars Coefficients) p.commutes
  obtain ⟨X, Y, hX₁, hY₁, hXY⟩ := AffineHopfTorsor.exists_lifted_inverse_of_kummer_weight_descent
    (k := Coefficients) (Q := Q) (S := S) (H := H) T₀ p j hj χ hχ x y hx hy c u hProdS
  exact ⟨q, hq, X, Y, fun i => (hX₁ i).trans (hSpec x₀ i), fun i => (hY₁ i).trans (hSpec y₀ i), hXY⟩

/-- Every wide E-value unit is an algebraic scalar times the exponential of an algebraic number. -/
theorem algebraic_scalar_exp_of_wideEValueUnit {ξ : ℂ} (hξ : IsWideEValueUnit ξ) :
    IsAlgebraicScalarExp ξ := by
  obtain ⟨data⟩ := exists_wideInverseModule wideLaurentOperatorExistence hξ
  let M := data.M
  let N : Submodule R WidePunctured := M * M
  let d := (D).toLinearMap.toAddMonoidHom
  have hN : ∀ x ∈ N, d x ∈ N :=
    productModule_stable d data.stable (fun x y => widePuncturedDerivation_mul x y)
  obtain ⟨m, ⟨bM⟩⟩ := exists_fin_basis_of_stable M data.finite data.stable
  obtain ⟨n, ⟨bN⟩⟩ := exists_fin_basis_of_stable N (productModule_fg data.finite) hN
  obtain ⟨q, hq, X, Y, hX, _, hXY⟩ :=
    exists_kummer_inverse_coordinates M data.stable data.one_mem bM bN data.f data.g data.h data.factor
  let F := fun i => (bM i).val
  have hUV := ramifiedModuleRealization_mul M data.one_mem bM bN q X Y hXY
  have hValue := (ramifiedModuleRealization_atOne bM data.f q X hX).trans data.value_f
  rw [← hValue]
  exact ramifiedModuleUnit_atOne hq F X (ramifiedModuleRealization q F Y) hUV

/-- The classification of numerical units among the wide E-values. -/
theorem wideEValueUnit_iff_algebraicScalarExp (ξ : ℂ) :
    IsWideEValueUnit ξ ↔ IsAlgebraicScalarExp ξ :=
  ⟨algebraic_scalar_exp_of_wideEValueUnit, algebraic_scalar_exp_isWideEValueUnit⟩

/-- The units of the actual wide E-value subring. -/
theorem isUnit_valueSubring_iff_algebraicScalarExp (u : valueSubring) :
    IsUnit u ↔ IsAlgebraicScalarExp (u : ℂ) :=
  (wideEValueUnit_iff_isUnit u).symm.trans (wideEValueUnit_iff_algebraicScalarExp u)

end WideE
