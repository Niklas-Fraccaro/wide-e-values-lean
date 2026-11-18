import WideE.TorsorBaseChange
import WideE.TorsorWeightDescent

/-! A pointed Kummer pullback descends an inverse relation of opposite weights. -/

open scoped TensorProduct WideE

noncomputable section

namespace WideE

open StrictEUnit

attribute [local instance 2000] Algebra.toModule

namespace AffineHopfTorsor

variable {k Q S H ι κ : Type*} [Field k] [CommRing Q] [CommRing S] [CommRing H]
variable [Algebra k Q] [Algebra k S] [Algebra Q S] [IsScalarTower k Q S] [HopfAlgebra k H]
variable [Algebra (LaurentPolynomial k) Q] [Algebra (LaurentPolynomial k) S]
variable [IsScalarTower k (LaurentPolynomial k) Q] [IsScalarTower (LaurentPolynomial k) Q S]
variable [Fintype ι] {q : ℕ}

local notation "LaurentBase" => LaurentPolynomial k
local notation "B" => KummerExtension k q

/-- Lift the given inverse coordinates over the pointed Kummer cover and
recover the original coordinates after specialization at one. -/
theorem exists_lifted_inverse_of_kummer_weight_descent
    (T : AffineHopfTorsor k Q S H) (p : S →ₐ[LaurentBase] k) (j : Q →ₐ[LaurentBase] B)
    (hj : ∀ a : Q, evalAtOne k (KummerExtension.toLaurent k q (j a)) =
      p (algebraMap Q S a))
    (χ : Hˣ) (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (x y : ι → S)
    (hx : ∀ i, T.coaction (x i) = x i ⊗ₜ[k] (χ : H))
    (hy : ∀ i, T.coaction (y i) = y i ⊗ₜ[k] (↑χ⁻¹ : H))
    (c : ι → ι → κ → LaurentBase) (d : κ → LaurentBase)
    (hProd : coordinateProduct (fun i j l => algebraMap LaurentBase S (c i j l)) x y =
      fun l => algebraMap LaurentBase S (d l)) :
    ∃ X Y : ι → LaurentBase, (∀ i, evalAtOne k (X i) = p (x i)) ∧
      (∀ i, evalAtOne k (Y i) = p (y i)) ∧
      coordinateProduct (fun i j l => kummer k q (c i j l)) X Y = fun l => kummer k q (d l) := by
  letI : Algebra Q B := j.toRingHom.toAlgebra
  letI : IsScalarTower k Q B := IsScalarTower.of_algHom (j.restrictScalars k)
  let e : B →+* LaurentBase := (KummerExtension.toLaurent k q).toRingHom
  let eval : B →ₐ[k] k :=
    { toRingHom := (evalAtOne k).comp e
      commutes' := fun a => evalAtOne_C k a }
  let evalQ := eval.comp (j.restrictScalars k)
  letI : Algebra Q k := evalQ.toRingHom.toAlgebra
  letI : IsScalarTower k Q k := IsScalarTower.of_algHom evalQ
  let evalBQ : B →ₐ[Q] k :=
    { toRingHom := eval.toRingHom
      commutes' := fun _ => rfl }
  let pQ : S →ₐ[Q] k :=
    { toRingHom := p.toRingHom
      commutes' := fun a => (hj a).symm }
  let P := KummerComponentPullback j S
  let T' : AffineHopfTorsor k B P H := T.kummerComponent j
  let iS : S →ₐ[Q] P := Algebra.TensorProduct.includeRight
  let p' : P →ₐ[k] k :=
    (Algebra.TensorProduct.lift (R := Q) (S := Q) evalBQ pQ
      (fun _ _ => Commute.all _ _)).restrictScalars k
  have hAtBase (b : B) : p' (algebraMap B P b) = eval b := by
    change eval b * pQ 1 = eval b
    rw [map_one, mul_one]
  have hAtS (s : S) : p' (iS s) = p s := by
    change eval 1 * pQ s = p s
    rw [map_one, one_mul]
    rfl
  have hBase (a : LaurentBase) : iS (algebraMap LaurentBase S a) = algebraMap B P (algebraMap LaurentBase B a) := by
    rw [IsScalarTower.algebraMap_apply LaurentBase Q S, iS.commutes, IsScalarTower.algebraMap_apply Q B P]
    exact congrArg (algebraMap B P) (j.commutes a)
  have hWeight (s : S) (h : H) (hs : T.coaction s = s ⊗ₜ[k] h) :
      T'.coaction (iS s) = iS s ⊗ₜ[k] h := by
    change (T.baseChange (A := B)).coaction ((1 : B) ⊗ₜ[Q] s) =
      ((1 : B) ⊗ₜ[Q] s) ⊗ₜ[k] h
    rw [baseChange_coaction_tmul, hs]
    rfl
  let x' := iS ∘ x
  let y' := iS ∘ y
  let c' := fun a b l => algebraMap LaurentBase B (c a b l)
  let d' := fun l => algebraMap LaurentBase B (d l)
  have hProd' :
      coordinateProduct (fun a b l => algebraMap B P (c' a b l)) x' y' =
        fun l => algebraMap B P (d' l) := by
    funext l
    have h := congrArg iS.toRingHom (congrFun hProd l)
    rw [map_coordinateProduct] at h
    change coordinateProduct (fun a b m => iS (algebraMap LaurentBase S (c a b m)))
      x' y' l = iS (algebraMap LaurentBase S (d l)) at h
    simpa only [hBase, c', d'] using h
  letI : IsDomain B := inferInstanceAs (IsDomain LaurentBase)
  letI : IsPrincipalIdealRing B := inferInstanceAs (IsPrincipalIdealRing LaurentBase)
  obtain ⟨u, X, Y, hu, _, hX, hY⟩ := T'.exists_normalized_weight_descent p' χ hχ x' y'
    (fun a => hWeight _ _ (hx a)) (fun a => hWeight _ _ (hy a))
  have huInv : p' (↑u⁻¹ : P) = 1 := by
    have h := congrArg p' (Units.inv_mul u)
    rwa [map_mul, hu, mul_one, map_one] at h
  refine ⟨e ∘ X, e ∘ Y, ?_, ?_, ?_⟩
  · intro a
    change eval (X a) = p (x a)
    rw [← hAtBase (X a), hX a, map_mul, huInv, one_mul]
    exact hAtS (x a)
  · intro a
    change eval (Y a) = p (y a)
    rw [← hAtBase (Y a), hY a, map_mul, hu, one_mul]
    exact hAtS (y a)
  · have h := T'.coordinateProduct_eq_of_weight_descent u c' d' x' y' X Y hX hY hProd'
    funext l
    simpa only [map_coordinateProduct] using congrArg e (congrFun h l)

end AffineHopfTorsor

end WideE
