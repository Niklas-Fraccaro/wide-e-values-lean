import WideE.PositiveKostantNormalizer
import WideE.HopfAdjointLieEquiv
import WideE.SimpleCoreflectionChamber

/-! Conjugation of two regular Cartan elements induces a permutation of roots. -/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling LieModule Module

namespace WideE

section Derived

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]

private theorem map_mem_derived (g : L ≃ₗ⁅k⁆ L) {x : L}
    (hx : x ∈ derivedSeries k L 1) : g x ∈ derivedSeries k L 1 := by
  have h := LieIdeal.derivedSeries_map_eq 1 (f := g.toLieHom) g.surjective
  rw [← h]
  exact LieIdeal.mem_map (f := g.toLieHom) hx

/-- An automorphism acts on the first derived ideal. -/
def lieEquivOnDerived (g : L ≃ₗ⁅k⁆ L) : (derivedSeries k L 1) ≃ₗ⁅k⁆ (derivedSeries k L 1) where
  toFun x := ⟨g x.val, map_mem_derived g x.prop⟩
  invFun x := ⟨g.symm x.val, map_mem_derived g.symm x.prop⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (g.toLieHom.map_add x.val y.val)
  map_smul' r x := Subtype.ext (g.toLieHom.map_smul r x.val)
  map_lie' := fun {x y} => Subtype.ext (g.toLieHom.map_lie x.val y.val)

@[simp] theorem lieEquivOnDerived_apply_val (g : L ≃ₗ⁅k⁆ L) (x : derivedSeries k L 1) :
    (lieEquivOnDerived g x : L) = g (x : L) := rfl

end Derived

section Cartan

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [IsKilling k L] [FiniteDimensional k L]
  {C : LieSubalgebra k L} [C.IsCartanSubalgebra] [IsTriangularizable k C L]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem C

/-- A Lie automorphism taking one regular Cartan vector to another restricts to the Cartan. -/
def cartanEquivOfRegularConjugation (g : L ≃ₗ⁅k⁆ L) (z w : C)
    (hz : ∀ α : C.root, (Φ).root α z ≠ 0) (hw : ∀ α : C.root, (Φ).root α w ≠ 0)
    (hg : g (z : L) = (w : L)) : C ≃ₗ[k] C where
  toFun x := ⟨g x.val, (lie_regularCartan_eq_zero_iff_mem w hw (g x.val)).mp (by
    rw [← hg]
    change ⁅g.toLieHom (z : L), g.toLieHom (x : L)⁆ = 0
    rw [← g.toLieHom.map_lie, (lie_regularCartan_eq_zero_iff_mem z hz _).mpr x.prop,
      g.toLieHom.map_zero])⟩
  invFun x := ⟨g.symm x.val, (lie_regularCartan_eq_zero_iff_mem z hz (g.symm x.val)).mp (by
    have h : g.symm (w : L) = (z : L) := by rw [← hg, g.symm_apply_apply]
    rw [← h]
    change ⁅g.symm.toLieHom (w : L), g.symm.toLieHom (x : L)⁆ = 0
    rw [← g.symm.toLieHom.map_lie, (lie_regularCartan_eq_zero_iff_mem w hw _).mpr x.prop,
      g.symm.toLieHom.map_zero])⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (g.toLieHom.map_add x.val y.val)
  map_smul' r x := Subtype.ext (g.toLieHom.map_smul r x.val)

/-- A Lie automorphism normalizing a split Cartan permutes the actual roots. -/
theorem exists_rootPerm_of_cartanEquiv (g : L ≃ₗ⁅k⁆ L) (c : C ≃ₗ[k] C)
    (hc : ∀ z : C, (c z : L) = g (z : L)) :
    ∃ p : Equiv.Perm C.root, ∀ (α : C.root) (z : C), (Φ).root α (c z) = (Φ).root (p α) z := by
  classical
  have hCandidate (α : C.root) : ∃ β : C.root, ∀ z : C,
      (Φ).root β z = (Φ).root α (c.symm z) := by
    let β (z : C) := (Φ).root α (c.symm z)
    letI : Nontrivial (rootSpace C α.val) :=
      (LieSubmodule.nontrivial_iff_ne_bot k C L).mpr α.val.genWeightSpace_ne_bot
    obtain ⟨v, hv⟩ := exists_ne (0 : rootSpace C α.val)
    have hG : g (v : L) ∈ rootSpace C β := by
      apply (LieModule.mem_genWeightSpace L β _).mpr
      intro z
      refine ⟨1, ?_⟩
      have hz : g (c.symm z : L) = (z : L) := by rw [← hc, c.apply_symm_apply]
      have hvz : ⁅(c.symm z : L), (v : L)⁆ = β z • (v : L) :=
        lie_eq_smul_of_mem_rootSpace v.prop (c.symm z)
      rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        LieModule.toEnd_apply_apply]
      change ⁅(z : L), g (v : L)⁆ - β z • g (v : L) = 0
      rw [← hz]
      change ⁅g.toLieHom (c.symm z : L), g.toLieHom (v : L)⁆ - β z • g.toLieHom (v : L) = 0
      rw [← g.toLieHom.map_lie, hvz, g.toLieHom.map_smul, sub_self]
    have hNe : g (v : L) ≠ 0 := fun h => hv (Subtype.ext (g.injective (h.trans g.toLieHom.map_zero.symm)))
    let b : Weight k C L := ⟨β, fun he => by
      rw [show rootSpace C β = ⊥ from he] at hG
      exact hNe hG⟩
    have hb : b.IsNonZero := by
      intro h
      apply (Finset.mem_filter.mp α.prop).2
      funext z
      have h' := congrFun h (c z)
      change (Φ).root α (c.symm (c z)) = 0 at h'
      rw [c.symm_apply_apply] at h'
      exact h'
    exact ⟨⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩,
      fun _ => rfl⟩
  choose p hp using hCandidate
  have hInj : Function.Injective p := by
    intro α β he
    apply Subtype.ext
    apply Weight.ext
    intro z
    have h := congrArg (fun r : C.root => (Φ).root r (c z)) he
    change (Φ).root (p α) (c z) = (Φ).root (p β) (c z) at h
    rw [hp, hp, c.symm_apply_apply] at h
    exact h
  let q := Equiv.ofBijective p ⟨hInj, Finite.surjective_of_injective hInj⟩
  refine ⟨q.symm, fun α z => ?_⟩
  have h := hp (q.symm α) (c z)
  change (Φ).root (q (q.symm α)) (c z) = _ at h
  rw [q.apply_symm_apply, c.symm_apply_apply] at h
  exact h

end Cartan

end WideE
