import WideE.OrbitMapFlatness
import Mathlib.RingTheory.Flat.Stability

/-!
# Faithful flatness of the orbit map along a primitive point

The point has nonzero coordinates at every closed point of its base.
Each such point therefore lifts along the scaled orbit map of a closed
projective orbit. Base-change flatness and these lifts prove faithfulness.
-/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

section BaseChange

variable {k A B S : Type*} [Field k] [IsAlgClosed k]
  [CommRing A] [CommRing B] [CommRing S]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra A B] [Algebra A S]
  [IsScalarTower k A B] [IsScalarTower k A S]

theorem faithfullyFlat_tensorProduct_of_lift_kPoints
    [Module.Flat A B] [Algebra.FiniteType k S]
    (hLift : ∀ p : S →ₐ[k] k, ∃ q : B →ₐ[k] k,
      q.comp (IsScalarTower.toAlgHom k A B) = p.comp (IsScalarTower.toAlgHom k A S)) :
    Module.FaithfullyFlat S (S ⊗[A] B) := by
  apply faithfullyFlat_of_lift_kPoints (k := k)
  intro p
  obtain ⟨q, hq⟩ := hLift p
  let e := p.comp (IsScalarTower.toAlgHom k A S)
  letI : Algebra A k := e.toRingHom.toAlgebra
  letI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  let pA : S →ₐ[A] k := ⟨p.toRingHom, fun _ => rfl⟩
  let qA : B →ₐ[A] k := ⟨q.toRingHom, fun a => DFunLike.congr_fun hq a⟩
  let f := (Algebra.TensorProduct.lift pA qA (fun _ _ => Commute.all _ _)).restrictScalars k
  refine ⟨f, AlgHom.ext fun s => ?_⟩
  change Algebra.TensorProduct.lift pA qA (fun _ _ => Commute.all _ _) (s ⊗ₜ[A] (1 : B)) = p s
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

end BaseChange

section PrimitiveOrbit

universe u

variable {k H ι : Type u} {S : Type*}
  [Field k] [IsAlgClosed k] [CommRing H] [IsDomain H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-- The actual affine pullback of the scaled orbit map at a primitive
vector on a closed projective orbit is faithfully flat. -/
theorem orbitConeMap_primitiveBaseChange_faithfullyFlat
    (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (v : ι → k) (g : OrbitConeAlgebra U.val v →ₐ[k] S)
    (hPrimitive : Ideal.span (Set.range (g ∘ orbitConeCoordinate U.val v)) = ⊤)
    (hOrbit : ∀ x : ι → k, x ≠ 0 →
      (∀ P ∈ orbitConeIdeal U.val v, MvPolynomial.aeval x P = 0) →
      ∃ (q : H →ₐ[k] k) (c : kˣ), x = (c : k) • (U.val.map q.toRingHom *ᵥ v)) :
    letI : Algebra (OrbitConeAlgebra U.val v) S := g.toRingHom.toAlgebra
    letI : Algebra (OrbitConeAlgebra U.val v) (LaurentPolynomial H) :=
      (orbitConeMap U.val v).toRingHom.toAlgebra
    Module.FaithfullyFlat S (S ⊗[OrbitConeAlgebra U.val v] LaurentPolynomial H) := by
  let D := OrbitConeAlgebra U.val v
  let B := LaurentPolynomial H
  let f := orbitConeMap U.val v
  letI : Algebra D S := g.toRingHom.toAlgebra
  letI : Algebra D B := f.toRingHom.toAlgebra
  letI : IsScalarTower k D S := IsScalarTower.of_algebraMap_eq (R := k) (S := D) (A := S)
    fun x => (g.commutes x).symm
  letI : IsScalarTower k D B := IsScalarTower.of_algebraMap_eq (R := k) (S := D) (A := B)
    fun x => (f.commutes x).symm
  letI : Module.Flat D B := flat_algebraMap_iff.mp (orbitConeMap_flat U hU v)
  apply faithfullyFlat_tensorProduct_of_lift_kPoints (k := k)
  intro p
  let x := (p.comp g) ∘ orbitConeCoordinate U.val v
  have hx : x ≠ 0 := by
    intro hZero
    have hLe : Ideal.span (Set.range (g ∘ orbitConeCoordinate U.val v)) ≤
        RingHom.ker p.toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (congrFun hZero i)
    apply RingHom.ker_ne_top p.toRingHom
    exact top_le_iff.mp (hPrimitive ▸ hLe)
  obtain ⟨q, c, hEq⟩ := hOrbit x hx (orbitConePoint_vanishes U.val v (p.comp g))
  exact ⟨laurentOrbitPoint q c, orbitConeMap_lift_of_coordinates U.val v (p.comp g) q c hEq⟩

end PrimitiveOrbit

end WideE
