import WideE.MultiplicativeTorsor
import WideE.Comparison
import CanonicalInvariants
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! Descend two opposite character weights to coordinates over the base. -/

open scoped TensorProduct

noncomputable section

namespace WideE

open StrictEUnit

attribute [local instance 2000] Algebra.toModule

namespace AffineHopfTorsor

variable {k B S H : Type*} [CommRing k] [CommRing B] [CommRing S] [CommRing H]
variable [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H]

/-- Faithful flatness makes the base map of the torsor injective. -/
theorem algebraMap_injective (T : AffineHopfTorsor k B S H) :
    Function.Injective (algebraMap B S) := by
  letI := T.faithfullyFlat
  have h := Module.FaithfullyFlat.tensorProduct_mk_injective (A := B) (B := S) B
  have ht (b : B) : TensorProduct.rid B S ((1 : S) ⊗ₜ[B] b) = algebraMap B S b :=
    (TensorProduct.rid_tmul (1 : S) b).trans (Algebra.algebraMap_eq_smul_one b).symm
  intro b c he
  apply h
  apply (TensorProduct.rid B S).injective
  exact (ht b).trans (he.trans (ht c).symm)

/-- A fixed element of the constant-group coaction comes from the base. -/
theorem exists_baseScalar_of_invariant (T : AffineHopfTorsor k B S H) (s : S)
    (hs : T.coaction s = s ⊗ₜ[k] (1 : H)) :
    ∃ b : B, algebraMap B S b = s := by
  letI := T.faithfullyFlat
  letI := baseChangeBialgebra (k := k) (H := H) B
  apply canonical_torsor_invariants_are_scalars (scalarTargetCoaction T.coaction)
    (scalarTargetCoaction_canonical_bijective T.coaction T.canonical_bijective)
    (scalarTargetCoaction_coassoc T.coaction T.coassociative) s
  change scalarTargetCoaction T.coaction s = s ⊗ₜ[B] ((1 : B) ⊗ₜ[k] (1 : H))
  exact (scalarTargetCoaction_weight_iff T.coaction s 1).mpr hs

private theorem opposite_weight_of_unit (T : AffineHopfTorsor k B S H) (u : Sˣ) (χ : Hˣ)
    (hu : T.coaction (u : S) = (u : S) ⊗ₜ[k] (χ : H)) :
    T.coaction (↑u⁻¹ : S) = (↑u⁻¹ : S) ⊗ₜ[k] (↑χ⁻¹ : H) := by
  apply ((u.isUnit.map T.coaction).mul_right_inj).mp
  rw [← map_mul, Units.mul_inv, map_one, hu, Algebra.TensorProduct.tmul_mul_tmul,
    Units.mul_inv, Units.mul_inv, Algebra.TensorProduct.one_def]

/-- A normalized unit of the first weight untwists both families into the base. -/
theorem exists_normalized_weight_descent [IsDomain B] [IsPrincipalIdealRing B] {ι : Type*}
    (T : AffineHopfTorsor k B S H) (p : S →ₐ[k] k)
    (χ : Hˣ) (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (x y : ι → S)
    (hx : ∀ i, T.coaction (x i) = x i ⊗ₜ[k] (χ : H))
    (hy : ∀ i, T.coaction (y i) = y i ⊗ₜ[k] (↑χ⁻¹ : H)) :
    ∃ (u : Sˣ) (X Y : ι → B), p (u : S) = 1 ∧
      T.coaction (u : S) = (u : S) ⊗ₜ[k] (χ : H) ∧
      (∀ i, algebraMap B S (X i) = (↑u⁻¹ : S) * x i) ∧
      (∀ i, algebraMap B S (Y i) = (u : S) * y i) := by
  classical
  obtain ⟨v, hv⟩ := T.exists_grouplike_unit χ hχ
  let c := Units.map p.toMonoidHom v
  let u := Units.map (algebraMap k S).toMonoidHom c⁻¹ * v
  have hp : p (u : S) = 1 := by
    change p (algebraMap k S (↑c⁻¹ : k) * (v : S)) = 1
    rw [map_mul, p.commutes]
    exact Units.inv_mul c
  have hScalar (a : k) : T.coaction (algebraMap k S a) =
      algebraMap k S a ⊗ₜ[k] (1 : H) :=
    (T.coaction.restrictScalars k).commutes a
  have hu : T.coaction (u : S) = (u : S) ⊗ₜ[k] (χ : H) := by
    change T.coaction (algebraMap k S (↑c⁻¹ : k) * (v : S)) =
      (algebraMap k S (↑c⁻¹ : k) * (v : S)) ⊗ₜ[k] (χ : H)
    rw [map_mul, hScalar, hv, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hInv := T.opposite_weight_of_unit u χ hu
  have hX (i : ι) : ∃ a : B, algebraMap B S a = (↑u⁻¹ : S) * x i := by
    apply T.exists_baseScalar_of_invariant
    rw [map_mul, hInv, hx i, Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul]
  have hY (i : ι) : ∃ a : B, algebraMap B S a = (u : S) * y i := by
    apply T.exists_baseScalar_of_invariant
    rw [map_mul, hu, hy i, Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv]
  choose X hX using hX
  choose Y hY using hY
  exact ⟨u, X, Y, hp, hu, hX, hY⟩

/-- Normalization by opposite units preserves any bilinear coordinate product,
and faithful flatness descends the resulting equation to the base. -/
theorem coordinateProduct_eq_of_weight_descent {ι κ : Type*} [Fintype ι]
    (T : AffineHopfTorsor k B S H) (u : Sˣ) (c : ι → ι → κ → B) (d : κ → B)
    (x y : ι → S) (X Y : ι → B)
    (hX : ∀ i, algebraMap B S (X i) = (↑u⁻¹ : S) * x i)
    (hY : ∀ i, algebraMap B S (Y i) = (u : S) * y i)
    (h : coordinateProduct (fun i j l => algebraMap B S (c i j l)) x y = fun l => algebraMap B S (d l)) :
    coordinateProduct c X Y = d := by
  let f := algebraMap B S
  have hX' : f ∘ X = (↑u⁻¹ : S) • x := funext hX
  have hY' : f ∘ Y = (u : S) • y := funext hY
  funext l
  apply T.algebraMap_injective
  change f (coordinateProduct c X Y l) = f (d l)
  rw [map_coordinateProduct, hX', hY']
  simp only [map_smul, LinearMap.smul_apply, smul_smul, Units.inv_mul, Units.mul_inv, one_smul]
  exact congrFun h l

end AffineHopfTorsor

end WideE
