import WideE.PVComponents
import WideE.FiniteDescent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Pi

/-! The quotient by the component projection splits over the affine torsor. -/

noncomputable section

open scoped TensorProduct

namespace WideE

open StrictEUnit

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

set_option maxHeartbeats 950000

section Quotient

variable {k B S H J : Type*} [CommRing k] [CommRing B] [CommRing S] [CommRing H] [CommRing J]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H] [Algebra k J]
  (T : AffineHopfTorsor k B S H) (j : J →ₐ[k] H) (r : H →ₐ[k] J)

local notation "M" => Algebra.TensorProduct.map
local notation "P" => (j.comp r)
local notation "Δ" => (Bialgebra.comulAlgHom k H)
local notation "ρ" => T.coaction

/-- The coaction followed by projection of the group factor to its component
scalars, viewed in the original target. -/
def componentProjectedCoaction : S →ₐ[B] S ⊗[k] H :=
  (M (AlgHom.id B S) P).comp ρ

/-- The functions whose coaction already uses only component scalars. -/
def componentQuotientAlgebra : Subalgebra B S :=
  AlgHom.equalizer (componentProjectedCoaction T j r) ρ

/-- The quotient equalizer depends only on the image of the component
inclusion, even when the algebra retraction was chosen. -/
theorem mem_componentQuotientAlgebra_iff (hj : Function.LeftInverse r j) (s : S) :
    s ∈ componentQuotientAlgebra T j r ↔
      ∃ x : S ⊗[k] J, M (AlgHom.id B S) j x = ρ s := by
  have hsplit : r.comp j = AlgHom.id k J := AlgHom.ext hj
  constructor
  · intro hs
    refine ⟨M (AlgHom.id B S) r (ρ s), ?_⟩
    change ((M (AlgHom.id B S) j).comp (M (AlgHom.id B S) r)) (ρ s) = ρ s
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
    exact hs
  · rintro ⟨x, hx⟩
    change M (AlgHom.id B S) P (ρ s) = ρ s
    rw [← hx]
    change ((M (AlgHom.id B S) P).comp (M (AlgHom.id B S) j)) x = M (AlgHom.id B S) j x
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_assoc, hsplit, AlgHom.comp_id]

private def mixedTriple :
    S ⊗[B] (S ⊗[k] H) ≃ₐ[k] S ⊗[k] (H ⊗[k] H) :=
  ((fiberMixedAssoc (k := k) (B := B) (A := S) (R := S) (H := H)).symm.restrictScalars k).trans
    ((Algebra.TensorProduct.congr (T.chart.symm.restrictScalars k)
      (AlgEquiv.refl (R := k) (A₁ := H))).trans (Algebra.TensorProduct.assoc k S H H))

private theorem mixedTriple_tmul (a s : S) (h : H) :
    mixedTriple T (a ⊗ₜ[B] (s ⊗ₜ[k] h)) =
      Algebra.TensorProduct.assoc k S H H (T.chart.symm (a ⊗ₜ[B] s) ⊗ₜ[k] h) := rfl

private theorem assoc_map_last (v : H →ₐ[k] H) (w : (S ⊗[k] H) ⊗[k] H) :
    Algebra.TensorProduct.assoc k S H H (M (AlgHom.id k (S ⊗[k] H)) v w) =
      M (AlgHom.id k S) (M (AlgHom.id k H) v) (Algebra.TensorProduct.assoc k S H H w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x h =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul a g => rfl

private theorem mixedTriple_map_last (v : H →ₐ[k] H) (a : S) (z : S ⊗[k] H) :
    mixedTriple T (a ⊗ₜ[B] (M (AlgHom.id B S) v) z) =
      M (AlgHom.id k S) (M (AlgHom.id k H) v) (mixedTriple T (a ⊗ₜ[B] z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | tmul s h =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, mixedTriple_tmul]
    exact assoc_map_last v (T.chart.symm (a ⊗ₜ[B] s) ⊗ₜ[k] h)

private theorem mixedTriple_apply (a : S) (z : S ⊗[k] H) :
    mixedTriple T (a ⊗ₜ[B] z) = (a ⊗ₜ[k] (1 : H ⊗[k] H)) *
      Algebra.TensorProduct.assoc k S H H (M ((ρ).restrictScalars k) (AlgHom.id k H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy, mul_add]
  | tmul s h =>
    rw [mixedTriple_tmul, T.chart_symm_apply, Algebra.TensorProduct.map_tmul,
      AlgHom.restrictScalars_apply, AlgHom.id_apply]
    rw [show (((a ⊗ₜ[k] (1 : H)) * ρ s) ⊗ₜ[k] h) =
        ((a ⊗ₜ[k] (1 : H)) ⊗ₜ[k] (1 : H)) * (ρ s ⊗ₜ[k] h) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
    rw [map_mul, Algebra.TensorProduct.assoc_tmul]
    rfl

private theorem mixedTriple_coaction (z : S ⊗[B] S) :
    mixedTriple T (M (AlgHom.id S S) ρ z) =
      M (AlgHom.id S S) Δ (T.chart.symm z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, mixedTriple_apply, T.coassociative,
      T.chart_symm_apply, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

private theorem mixedTriple_projectedCoaction (z : S ⊗[B] S) :
    mixedTriple T (M (AlgHom.id S S) (componentProjectedCoaction T j r) z) =
      M (AlgHom.id k S) (M (AlgHom.id k H) P) (mixedTriple T (M (AlgHom.id S S) ρ z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact mixedTriple_map_last T P s (ρ a)

private theorem componentQuotientMap_fixed (x : S ⊗[B] componentQuotientAlgebra T j r) :
    let w := T.chart.symm (M (AlgHom.id S S) (componentQuotientAlgebra T j r).val x)
    M (AlgHom.id S S) P w = w := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a q =>
    change M (AlgHom.id S S) P (T.chart.symm (a ⊗ₜ[B] (q : S))) =
      T.chart.symm (a ⊗ₜ[B] (q : S))
    rw [T.chart_symm_apply, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    exact congrArg ((a ⊗ₜ[k] (1 : H)) * ·) q.property

/-- A split component inclusion that is stable in the right comultiplication
factor trivializes the quotient after scalar extension along the torsor. -/
def componentQuotientBaseChangeChart (hj : Function.LeftInverse r j)
    (hstable : ∀ x : J, M (AlgHom.id k H) P (Δ (j x)) = Δ (j x)) :
    (S ⊗[B] componentQuotientAlgebra T j r) ≃ₐ[S] S ⊗[k] J := by
  letI := T.faithfullyFlat
  let Q := componentQuotientAlgebra T j r
  let f := componentProjectedCoaction T j r
  let E := AlgHom.tensorEqualizerEquiv S S f ρ
  let i := M (AlgHom.id S S) Q.val
  let W := T.chart.symm.toAlgHom.comp i
  let F := (M (AlgHom.id S S) r).comp W
  have hE (x : S ⊗[B] Q) : (E x : S ⊗[B] S) = i x := by
    simp only [E, AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]
    rfl
  have hi : Function.Injective i := by
    intro a b hab
    apply E.injective
    apply Subtype.ext
    exact (hE a).trans (hab.trans (hE b).symm)
  have hW : Function.Injective W := T.chart.symm.injective.comp hi
  have hrj : r.comp j = AlgHom.id k J := AlgHom.ext hj
  have hRecover (x : S ⊗[B] Q) : M (AlgHom.id S S) j (F x) = W x := by
    change ((M (AlgHom.id S S) j).comp (M (AlgHom.id S S) r)) (W x) = W x
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
    exact componentQuotientMap_fixed T j r x
  refine AlgEquiv.ofBijective F ⟨?_, ?_⟩
  · intro a b hab
    apply hW
    rw [← hRecover a, ← hRecover b, hab]
  · intro y
    let z := T.chart (M (AlgHom.id S S) j y)
    have hz : M (AlgHom.id S S) f z = M (AlgHom.id S S) ρ z := by
      apply (mixedTriple T).injective
      rw [mixedTriple_projectedCoaction, mixedTriple_coaction]
      have hz' : T.chart.symm z = M (AlgHom.id S S) j y := T.chart.symm_apply_apply _
      rw [hz']
      change ((M (AlgHom.id k S) (M (AlgHom.id k H) P)).comp
        ((M (AlgHom.id k S) Δ).comp (M (AlgHom.id k S) j))) y =
        ((M (AlgHom.id k S) Δ).comp (M (AlgHom.id k S) j)) y
      simp only [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_assoc]
      rw [show (M (AlgHom.id k H) P).comp ((Δ).comp j) = (Δ).comp j from AlgHom.ext hstable]
    let w : AlgHom.equalizer (M (AlgHom.id S S) f) (M (AlgHom.id S S) ρ) := ⟨z, hz⟩
    let x := E.symm w
    have hx : i x = z := (hE x).symm.trans (congrArg Subtype.val (E.apply_symm_apply w))
    refine ⟨x, ?_⟩
    change M (AlgHom.id S S) r (T.chart.symm (i x)) = y
    rw [hx, show T.chart.symm z = M (AlgHom.id S S) j y from T.chart.symm_apply_apply _]
    change ((M (AlgHom.id S S) r).comp (M (AlgHom.id S S) j)) y = y
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, hrj, Algebra.TensorProduct.map_id]
    rfl

/-- The quotient chart is compatible with the inclusion of component scalars
in the original torsor chart. -/
theorem componentQuotientBaseChangeChart_inclusion (hj : Function.LeftInverse r j)
    (hstable : ∀ x : J, M (AlgHom.id k H) P (Δ (j x)) = Δ (j x))
    (x : S ⊗[B] componentQuotientAlgebra T j r) :
    M (AlgHom.id S S) j (componentQuotientBaseChangeChart T j r hj hstable x) =
      T.chart.symm (M (AlgHom.id S S) (componentQuotientAlgebra T j r).val x) := by
  let w := T.chart.symm (M (AlgHom.id S S) (componentQuotientAlgebra T j r).val x)
  change ((M (AlgHom.id S S) j).comp (M (AlgHom.id S S) r)) w = w
  rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
  exact componentQuotientMap_fixed T j r x

/-- Finiteness of the component quotient descends along the torsor algebra. -/
theorem componentQuotient_finite [Module.Finite k J] (hj : Function.LeftInverse r j)
    (hstable : ∀ x : J, M (AlgHom.id k H) P (Δ (j x)) = Δ (j x)) :
    Module.Finite B (componentQuotientAlgebra T j r) := by
  letI := T.faithfullyFlat
  letI : Module.Finite S (S ⊗[B] componentQuotientAlgebra T j r) :=
    Module.Finite.equiv (componentQuotientBaseChangeChart T j r hj hstable).symm.toLinearEquiv
  exact finite_of_faithfullyFlat_tensor (S := S)

end Quotient

section Components

universe u

variable {k B S H : Type u} [Field k] [IsAlgClosed k] [CommRing B] [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H]
  (T : AffineHopfTorsor k B S H) (G : ComponentHopfPresentation k H)

private def componentRetraction : H →ₐ[k] (G.Index → k) :=
  letI := G.index_finite
  letI := T.group_finiteType
  componentPointRetraction G.idempotent G.connected

private theorem componentRetraction_leftInverse :
    Function.LeftInverse (componentRetraction T G) G.inclusion :=
  letI := G.index_finite
  letI := T.group_finiteType
  componentPointRetraction_inclusion G.idempotent G.complete G.connected

private theorem componentComul_stable (x : G.Index → k) :
    Algebra.TensorProduct.map (AlgHom.id k H) (G.inclusion.comp (componentRetraction T G))
      (Bialgebra.comulAlgHom k H (G.inclusion x)) = Bialgebra.comulAlgHom k H (G.inclusion x) := by
  letI := T.group_finiteType
  letI := G.hopf
  let j := G.inclusion
  let r := componentRetraction T G
  have hr : r.comp j = AlgHom.id k _ := AlgHom.ext (componentRetraction_leftInverse T G)
  rw [← G.comul x]
  change ((Algebra.TensorProduct.map (AlgHom.id k H) (j.comp r)).comp
    (Algebra.TensorProduct.map j j)) (Bialgebra.comulAlgHom k (G.Index → k) x) = _
  rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_assoc, hr, AlgHom.comp_id]

/-- The quotient torsor's coordinate algebra, formed inside the original torsor. -/
def componentTorsorQuotient : Subalgebra B S :=
  componentQuotientAlgebra T G.inclusion (componentRetraction T G)

/-- Pulling the quotient back along the torsor gives the component algebra
extended from the constant field. -/
def componentTorsorQuotientChart :
    (S ⊗[B] componentTorsorQuotient T G) ≃ₐ[S] S ⊗[k] (G.Index → k) :=
  componentQuotientBaseChangeChart T G.inclusion (componentRetraction T G)
    (componentRetraction_leftInverse T G) (componentComul_stable T G)

/-- The chart of the component quotient agrees with the original chart
under the inclusion of the two coordinate algebras. -/
theorem componentTorsorQuotientChart_inclusion (x : S ⊗[B] componentTorsorQuotient T G) :
    Algebra.TensorProduct.map (AlgHom.id S S) G.inclusion (componentTorsorQuotientChart T G x) =
      T.chart.symm (Algebra.TensorProduct.map (AlgHom.id S S) (componentTorsorQuotient T G).val x) :=
  componentQuotientBaseChangeChart_inclusion T G.inclusion (componentRetraction T G)
    (componentRetraction_leftInverse T G) (componentComul_stable T G) x

theorem mem_componentTorsorQuotient_iff (s : S) :
    s ∈ componentTorsorQuotient T G ↔ ∃ x : S ⊗[k] (G.Index → k),
      Algebra.TensorProduct.map (AlgHom.id B S) G.inclusion x = T.coaction s :=
  mem_componentQuotientAlgebra_iff T G.inclusion (componentRetraction T G)
    (componentRetraction_leftInverse T G) s

/-- The pulled-back quotient is a finite disjoint union of copies of the base. -/
def componentTorsorQuotient_split :
    (S ⊗[B] componentTorsorQuotient T G) ≃ₐ[S] (G.Index → S) := by
  classical
  letI := G.index_finite
  exact (componentTorsorQuotientChart T G).trans
    ((Algebra.TensorProduct.piRight k S S (fun _ : G.Index => k)).trans
      (AlgEquiv.piCongrRight (fun _ : G.Index => Algebra.TensorProduct.rid k S S)))

theorem componentTorsorQuotient_finite : Module.Finite B (componentTorsorQuotient T G) :=
  letI := G.finite
  componentQuotient_finite T G.inclusion (componentRetraction T G)
    (componentRetraction_leftInverse T G) (componentComul_stable T G)

theorem componentTorsorQuotient_etale_after_baseChange :
    Algebra.Etale S (S ⊗[B] componentTorsorQuotient T G) :=
  letI := G.etale
  Algebra.Etale.of_equiv (componentTorsorQuotientChart T G).symm

end Components

end WideE
