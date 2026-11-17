import WideE.ConnectedTensor
import WideE.FiniteEtaleComponent
import WideE.PVTorsor
import WideE.HopfRestriction
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Etale.Pi

/-! The finite algebra of functions on the connected components of an affine group. -/

noncomputable section

open scoped TensorProduct BigOperators WideE

namespace WideE

open Set TopologicalSpace StrictEUnit

private theorem finite_connectedComponents {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] : Finite (ConnectedComponents X) := by
  classical
  letI : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let p (Z : irreducibleComponents X) : X := Classical.choose Z.property.1.nonempty
  have hp (Z : irreducibleComponents X) : p Z ∈ Z.val :=
    Classical.choose_spec Z.property.1.nonempty
  apply Finite.of_surjective (fun Z => ConnectedComponents.mk (p Z))
  intro i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  let Z : irreducibleComponents X := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  refine ⟨Z, ConnectedComponents.coe_eq_coe'.mpr ?_⟩
  exact irreducibleComponent_subset_connectedComponent (hp Z)

private theorem idempotent_eq_of_basicOpen_eq {R : Type*} [CommRing R] {e f : R}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) = PrimeSpectrum.basicOpen f) : e = f := by
  let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
  have h' : E ⟨e, he⟩ = E ⟨f, hf⟩ := by
    apply Clopens.ext
    exact h
  exact congrArg Subtype.val (E.injective h')

universe u

private theorem algebraEtale_self (R : Type u) [CommRing R] : Algebra.Etale R R := by
  refine ⟨?_, inferInstance⟩
  constructor
  intro B _ _ I _
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨Algebra.ofId R B, Subsingleton.elim _ _⟩⟩

/-- The connected components of a Noetherian affine scheme give a finite
complete orthogonal decomposition by idempotents. -/
theorem exists_connected_component_idempotents (R : Type u) [CommRing R] [IsNoetherianRing R] :
    ∃ ι : Type u, ∃ hι : Fintype ι, ∃ e : ι → R,
      letI := hι
      CompleteOrthogonalIdempotents e ∧
      ∀ i, ConnectedSpace (PrimeSpectrum (QuotientComponent R (e i))) := by
  classical
  letI : Algebra.Etale R R := algebraEtale_self R
  let ι := ConnectedComponents (PrimeSpectrum R)
  letI : Finite ι := finite_connectedComponents
  letI : Fintype ι := Fintype.ofFinite ι
  choose x hx using fun i : ι => ConnectedComponents.surjective_coe i
  choose e he hRange hConn _ _ using fun i : ι =>
    exists_finite_etale_quotientComponent (R := R) (Q := R) (x i)
  have hOpen (i : ι) : (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum R)) = connectedComponent (x i) :=
    (quotientComponent_range R (he i)).symm.trans (hRange i)
  have hOrthogonal : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij => ?_⟩
    apply idempotent_eq_of_basicOpen_eq ((he i).mul (he j)) IsIdempotentElem.zero
    rw [PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_zero]
    change (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum R)) ∩
      (PrimeSpectrum.basicOpen (e j) : Set (PrimeSpectrum R)) = ∅
    rw [hOpen i, hOpen j]
    apply Set.disjoint_iff_inter_eq_empty.mp
    apply connectedComponent_disjoint
    intro h
    apply hij
    rw [← hx i, ← hx j]
    exact ConnectedComponents.coe_eq_coe.mpr h
  refine ⟨ι, inferInstance, e, ⟨hOrthogonal, ?_⟩, hConn⟩
  apply idempotent_eq_of_basicOpen_eq hOrthogonal.isIdempotentElem_sum IsIdempotentElem.one
  rw [PrimeSpectrum.basicOpen_one]
  apply Set.eq_univ_of_forall
  intro s
  let i : ι := ConnectedComponents.mk s
  have hs : s ∈ PrimeSpectrum.basicOpen (e i) := by
    change s ∈ (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum R))
    rw [hOpen i]
    exact ConnectedComponents.coe_eq_coe'.mp (hx i).symm
  change (∑ j, e j) ∉ s.asIdeal
  intro hs'
  exact hs ((hOrthogonal.mul_sum_of_mem (Finset.mem_univ i)) ▸ s.asIdeal.mul_mem_left (e i) hs')

section ComponentAlgebra

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [Algebra k H] [Algebra.FiniteType k H]
  {ι : Type u} [Fintype ι] (e : ι → H) (he : CompleteOrthogonalIdempotents e)
  (hconn : ∀ i, ConnectedSpace (PrimeSpectrum (QuotientComponent H (e i))))

local notation "Hc" => (fun i => QuotientComponent H (e i))

private def componentQuotient (i : ι) : H →ₐ[k] Hc i :=
  Ideal.Quotient.mkₐ k (Ideal.span {1 - e i})

private def componentDecomposition : H ≃ₐ[k] ∀ i, Hc i :=
  AlgEquiv.ofBijective (Pi.algHom k Hc (componentQuotient (k := k) e)) he.bijective_pi

include hconn in
omit [Fintype ι] in
private theorem componentQuotient_nontrivial (i : ι) : Nontrivial (Hc i) := by
  letI := hconn i
  let s : PrimeSpectrum (Hc i) := Classical.choice (show Nonempty (PrimeSpectrum (Hc i)) from inferInstance)
  apply nontrivial_of_ne 0 1
  intro h
  exact s.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (h ▸ s.asIdeal.zero_mem))

private def componentPoint (i : ι) : Hc i →ₐ[k] k :=
  haveI := componentQuotient_nontrivial e hconn i
  Classical.choice (nonempty_algebraic_point (k := k) (S := Hc i))

/-- The inclusion of the functions constant on each connected component. -/
def componentScalarInclusion : (ι → k) →ₐ[k] H :=
  (componentDecomposition (k := k) e he).symm.toAlgHom.comp
    (Pi.algHom k Hc (fun i => (Algebra.ofId k (Hc i)).comp (Pi.evalAlgHom k (fun _ : ι => k) i)))

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem componentQuotient_inclusion (i : ι) (a : ι → k) :
    componentQuotient (k := k) e i (componentScalarInclusion (k := k) e he a) = algebraMap k (Hc i) (a i) := by
  exact congrFun ((componentDecomposition (k := k) e he).apply_symm_apply
    (fun i => algebraMap k (Hc i) (a i))) i

omit [IsAlgClosed k] [Algebra.FiniteType k H] [Fintype ι] in
private theorem componentQuotient_idempotent_one (i : ι) :
    componentQuotient (k := k) e i (e i) = 1 := by
  have h : componentQuotient (k := k) e i (1 - e i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
/-- The indicator of a component includes as its defining idempotent. -/
theorem componentScalarInclusion_indicator [DecidableEq ι] (i : ι) :
    componentScalarInclusion (k := k) e he (Pi.single i (1 : k)) = e i := by
  apply (componentDecomposition (k := k) e he).injective
  funext j
  change componentQuotient (k := k) e j
      (componentScalarInclusion (k := k) e he (Pi.single i (1 : k))) =
    componentQuotient (k := k) e j (e i)
  rw [componentQuotient_inclusion]
  by_cases h : j = i
  · subst j
    rw [Pi.single_eq_same, map_one, componentQuotient_idempotent_one]
  · have hzero := congrArg (componentQuotient (k := k) e j) (he.ortho (Ne.symm h))
    rw [map_mul, componentQuotient_idempotent_one, mul_one, map_zero] at hzero
    simpa only [Pi.single_eq_of_ne h, map_zero] using hzero.symm

/-- Evaluating at one chosen point of every component gives a retraction. -/
def componentPointRetraction : H →ₐ[k] (ι → k) :=
  Pi.algHom k (fun _ : ι => k) (fun i => (componentPoint (k := k) e hconn i).comp (componentQuotient (k := k) e i))

@[simp] theorem componentPointRetraction_inclusion (a : ι → k) :
    componentPointRetraction (k := k) e hconn (componentScalarInclusion (k := k) e he a) = a := by
  funext i
  change componentPoint (k := k) e hconn i (componentQuotient (k := k) e i (componentScalarInclusion (k := k) e he a)) = a i
  rw [componentQuotient_inclusion, AlgHom.commutes]
  rfl

include hconn in
theorem componentScalarInclusion_injective : Function.Injective (componentScalarInclusion (k := k) e he) :=
  Function.LeftInverse.injective (componentPointRetraction_inclusion (k := k) e he hconn)

include he in
omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem point_factors_through_component (p : H →ₐ[k] k) :
    ∃ i : ι, ∃ p' : Hc i →ₐ[k] k, p = p'.comp (componentQuotient (k := k) e i) := by
  have hSome : ∃ i, p (e i) ≠ 0 := by
    by_contra! h
    have hs := congrArg p he.complete
    simp only [map_sum, map_one, h, Finset.sum_const_zero, zero_ne_one] at hs
  obtain ⟨i, hi⟩ := hSome
  have hi1 : p (e i) = 1 := (IsIdempotentElem.iff_eq_zero_or_one.mp ((he.idem i).map p)).resolve_left hi
  let J : Ideal H := Ideal.span {1 - e i}
  have hkill : J ≤ RingHom.ker p.toRingHom := by
    rw [Ideal.span_le, singleton_subset_iff]
    change p (1 - e i) = 0
    rw [map_sub, map_one, hi1, sub_self]
  exact ⟨i, Ideal.Quotient.liftₐ J p hkill, (Ideal.Quotient.liftₐ_comp J p hkill).symm⟩

/-- Projection onto the component scalars, expressed as an endomorphism of
the original coordinate algebra. -/
def componentScalarProjection : H →ₐ[k] H :=
  (componentScalarInclusion (k := k) e he).comp (componentPointRetraction (k := k) e hconn)

private theorem componentScalarProjection_at_point (p : H →ₐ[k] k) (i : ι)
    (p' : Hc i →ₐ[k] k) (hp : p = p'.comp (componentQuotient (k := k) e i)) :
    p.comp (componentScalarProjection (k := k) e he hconn) =
      (componentPoint (k := k) e hconn i).comp (componentQuotient (k := k) e i) := by
  apply AlgHom.ext
  intro z
  change p (componentScalarInclusion (k := k) e he (componentPointRetraction (k := k) e hconn z)) = _
  rw [hp]
  change p' (componentQuotient (k := k) e i (componentScalarInclusion (k := k) e he (componentPointRetraction (k := k) e hconn z))) = _
  rw [componentQuotient_inclusion, AlgHom.commutes]
  rfl

/-- Every idempotent on the affine scheme belongs to its component scalars. -/
theorem componentScalarProjection_idempotent {z : H} (hz : IsIdempotentElem z) :
    componentScalarProjection (k := k) e he hconn z = z := by
  apply idempotent_eq_of_points (k := k) (hz.map (componentScalarProjection (k := k) e he hconn)) hz
  intro p
  obtain ⟨i, p', hp⟩ := point_factors_through_component e he p
  have hp' : p (componentScalarProjection (k := k) e he hconn z) =
      componentPoint (k := k) e hconn i (componentQuotient (k := k) e i z) :=
    congrArg (fun f : H →ₐ[k] k => f z) (componentScalarProjection_at_point e he hconn p i p' hp)
  rw [hp', hp]
  letI := hconn i
  rcases idempotent_eq_zero_or_one_of_preconnected (hz.map (componentQuotient (k := k) e i)) with h | h
  · change componentPoint (k := k) e hconn i (componentQuotient (k := k) e i z) =
      p' (componentQuotient (k := k) e i z)
    rw [h, map_zero, map_zero]
  · change componentPoint (k := k) e hconn i (componentQuotient (k := k) e i z) =
      p' (componentQuotient (k := k) e i z)
    rw [h, map_one, map_one]

end ComponentAlgebra

section TensorPoints

variable {k A B U V : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing U] [CommRing V]
  [Algebra k A] [Algebra k B] [Algebra k U] [Algebra k V]

private def tensorPoint (p : A →ₐ[k] k) (q : B →ₐ[k] k) : A ⊗[k] B →ₐ[k] k :=
  Algebra.TensorProduct.lift p q (fun _ _ => Commute.all _ _)

private theorem tensorPoint_of_hom (p : A ⊗[k] B →ₐ[k] k) (z : A ⊗[k] B) :
    tensorPoint (p.comp Algebra.TensorProduct.includeLeft) (p.comp Algebra.TensorProduct.includeRight) z =
      p z := by
  have h : tensorPoint (p.comp Algebra.TensorProduct.includeLeft)
      (p.comp Algebra.TensorProduct.includeRight) = p := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change p (a ⊗ₜ[k] (1 : B)) * p ((1 : A) ⊗ₜ[k] b) = p (a ⊗ₜ[k] b)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact congrArg (fun f : A ⊗[k] B →ₐ[k] k => f z) h

private theorem tensorPoint_map (p : U →ₐ[k] k) (q : V →ₐ[k] k)
    (a : A →ₐ[k] U) (b : B →ₐ[k] V) (z : A ⊗[k] B) :
    tensorPoint p q (Algebra.TensorProduct.map a b z) = tensorPoint (p.comp a) (q.comp b) z := by
  have h : (tensorPoint p q).comp (Algebra.TensorProduct.map a b) =
      tensorPoint (p.comp a) (q.comp b) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rfl
  exact congrArg (fun f : A ⊗[k] B →ₐ[k] k => f z) h

end TensorPoints

section TensorIdempotents

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [Algebra k H] [Algebra.FiniteType k H]
  {ι : Type u} [Fintype ι] (e : ι → H) (he : CompleteOrthogonalIdempotents e)
  (hconn : ∀ i, ConnectedSpace (PrimeSpectrum (QuotientComponent H (e i))))

/-- The idempotents on the product algebra already come from the tensor
product of the two component scalar algebras. -/
theorem componentScalarProjection_tensor_idempotent {z : H ⊗[k] H} (hz : IsIdempotentElem z) :
    Algebra.TensorProduct.map (S := k) (componentScalarProjection (k := k) e he hconn)
      (componentScalarProjection (k := k) e he hconn) z = z := by
  letI : Algebra.FiniteType k (H ⊗[k] H) :=
    Algebra.FiniteType.trans (S := H) inferInstance inferInstance
  let P : H →ₐ[k] H := componentScalarProjection (k := k) e he hconn
  let M := Algebra.TensorProduct.map P P
  apply idempotent_eq_of_points (k := k) (hz.map M) hz
  intro v
  let p : H →ₐ[k] k := v.comp Algebra.TensorProduct.includeLeft
  let q : H →ₐ[k] k := v.comp Algebra.TensorProduct.includeRight
  obtain ⟨i, p', hp⟩ := point_factors_through_component e he p
  obtain ⟨j, q', hq⟩ := point_factors_through_component e he q
  let πi := componentQuotient (k := k) e i
  let πj := componentQuotient (k := k) e j
  let w := Algebra.TensorProduct.map πi πj z
  letI := hconn i
  letI := hconn j
  letI := componentQuotient_nontrivial e hconn j
  have hw : w = 0 ∨ w = 1 :=
    idempotent_tensor_eq_zero_or_one
      (fun _ h => idempotent_eq_zero_or_one_of_preconnected h)
      (fun _ h => idempotent_eq_zero_or_one_of_preconnected h)
      (hz.map (Algebra.TensorProduct.map πi πj))
  have h₀ : v z = tensorPoint p' q' w := by
    calc
      _ = tensorPoint p q z := (tensorPoint_of_hom v z).symm
      _ = _ := by rw [hp, hq]; exact (tensorPoint_map p' q' πi πj z).symm
  have h₁ : v (M z) = tensorPoint (componentPoint (k := k) e hconn i) (componentPoint (k := k) e hconn j) w := by
    calc
      _ = tensorPoint p q (M z) := (tensorPoint_of_hom v (M z)).symm
      _ = tensorPoint (p.comp P) (q.comp P) z := tensorPoint_map p q P P z
      _ = _ := by
        rw [componentScalarProjection_at_point e he hconn p i p' hp,
          componentScalarProjection_at_point e he hconn q j q' hq]
        exact (tensorPoint_map (componentPoint (k := k) e hconn i) (componentPoint (k := k) e hconn j) πi πj z).symm
  rw [h₀, h₁]
  rcases hw with hh | hh
  · rw [hh, map_zero, map_zero]
  · rw [hh, map_one, map_one]

end TensorIdempotents

section HopfStructure

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  {ι : Type u} [Fintype ι] (e : ι → H) (he : CompleteOrthogonalIdempotents e)
  (hconn : ∀ i, ConnectedSpace (PrimeSpectrum (QuotientComponent H (e i))))

omit [IsAlgClosed k] in
private theorem piAlgHom_ext_single {A : Type*} [CommRing A] [Algebra k A] [DecidableEq ι]
    {F G : (ι → k) →ₐ[k] A}
    (h : ∀ i, F (Pi.single i (1 : k)) = G (Pi.single i (1 : k))) : F = G := by
  apply AlgHom.ext
  intro c
  have hc : (∑ i, c i • Pi.single i (1 : k)) = c := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← hc]
  simp only [map_sum, map_smul, h]

omit [IsAlgClosed k] [Fintype ι] in
private theorem indicator_idempotent [DecidableEq ι] (i : ι) :
    IsIdempotentElem (Pi.single (f := fun _ : ι => k) i (1 : k)) := by
  let v : ι → k := Pi.single i 1
  change v * v = v
  funext j
  by_cases h : j = i <;> simp [v, Pi.single_apply, h]

private theorem component_comul_closed (x : ι → k) :
    let j := componentScalarInclusion (k := k) e he
    let r := componentPointRetraction (k := k) e hconn
    Algebra.TensorProduct.map (S := k) j j
      (Algebra.TensorProduct.map (S := k) r r (Bialgebra.comulAlgHom k H (j x))) =
        Bialgebra.comulAlgHom k H (j x) := by
  classical
  dsimp only
  let j := componentScalarInclusion (k := k) e he
  let r := componentPointRetraction (k := k) e hconn
  let E := Bialgebra.comulAlgHom k H
  have hP : (Algebra.TensorProduct.map (S := k) (j.comp r) (j.comp r)).comp (E.comp j) = E.comp j := by
    apply piAlgHom_ext_single
    intro i
    exact componentScalarProjection_tensor_idempotent e he hconn
      ((indicator_idempotent (k := k) i).map (E.comp j))
  have h := congrArg (fun f : (ι → k) →ₐ[k] H ⊗[k] H => f x) hP
  rw [Algebra.TensorProduct.map_comp] at h
  exact h

private theorem component_endomorphism_closed (S : H →ₐ[k] H) (x : ι → k) :
    componentScalarInclusion (k := k) e he (componentPointRetraction (k := k) e hconn (S (componentScalarInclusion (k := k) e he x))) =
      S (componentScalarInclusion (k := k) e he x) := by
  classical
  let j := componentScalarInclusion (k := k) e he
  let r := componentPointRetraction (k := k) e hconn
  have hP : (j.comp r).comp (S.comp j) = S.comp j := by
    apply piAlgHom_ext_single
    intro i
    exact componentScalarProjection_idempotent (k := k) e he hconn
      ((indicator_idempotent (k := k) i).map (S.comp j))
  exact congrArg (fun f : (ι → k) →ₐ[k] H => f x) hP

/-- The Hopf algebra of functions constant on the connected components.
An algebra-map presentation of the ambient antipode gives its restriction. -/
def componentScalarHopf (S : H →ₐ[k] H)
    (hS : S.toLinearMap = HopfAlgebra.antipode (R := k)) : HopfAlgebra k (ι → k) := by
  apply restrictHopfAlgebra
    (componentScalarInclusion (k := k) e he) (componentPointRetraction (k := k) e hconn)
    (componentPointRetraction_inclusion e he hconn) (component_comul_closed e he hconn)
  intro x
  change componentScalarInclusion (k := k) e he (componentPointRetraction (k := k) e hconn
    (HopfAlgebra.antipode (R := k) (componentScalarInclusion (k := k) e he x))) = _
  rw [← hS]
  exact component_endomorphism_closed e he hconn S x

/-- Inclusion preserves the comultiplication of the component algebra. -/
theorem componentScalarInclusion_comul (S : H →ₐ[k] H)
    (hS : S.toLinearMap = HopfAlgebra.antipode (R := k)) (x : ι → k) :
    letI := componentScalarHopf e he hconn S hS
    Algebra.TensorProduct.map (S := k) (componentScalarInclusion (k := k) e he)
      (componentScalarInclusion (k := k) e he) (Coalgebra.comul x) =
        Coalgebra.comul (R := k) (componentScalarInclusion (k := k) e he x) :=
  component_comul_closed e he hconn x

/-- Inclusion preserves the counit of the component algebra. -/
theorem componentScalarInclusion_counit (S : H →ₐ[k] H)
    (hS : S.toLinearMap = HopfAlgebra.antipode (R := k)) (x : ι → k) :
    letI := componentScalarHopf e he hconn S hS
    Coalgebra.counit (R := k) (componentScalarInclusion (k := k) e he x) =
      Coalgebra.counit (R := k) x := rfl

/-- Inclusion preserves the antipode of the component algebra. -/
theorem componentScalarInclusion_antipode (S : H →ₐ[k] H)
    (hS : S.toLinearMap = HopfAlgebra.antipode (R := k)) (x : ι → k) :
    letI := componentScalarHopf e he hconn S hS
    componentScalarInclusion (k := k) e he (HopfAlgebra.antipode (R := k) x) =
      HopfAlgebra.antipode (R := k) (componentScalarInclusion (k := k) e he x) := by
  letI := componentScalarHopf e he hconn S hS
  change componentScalarInclusion (k := k) e he (componentPointRetraction (k := k) e hconn
    (HopfAlgebra.antipode (R := k) (componentScalarInclusion (k := k) e he x))) = _
  rw [← hS]
  exact component_endomorphism_closed e he hconn S x

end HopfStructure

section Presentation

variable (k H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]

/-- The finitely many clopen components and the ambient antipode as an
algebra map. The component Hopf structure is defined from these data. -/
structure ComponentHopfPresentation where
  Index : Type u
  index_finite : Fintype Index
  idempotent : Index → H
  complete : letI := index_finite; CompleteOrthogonalIdempotents idempotent
  connected : ∀ i, ConnectedSpace (PrimeSpectrum (QuotientComponent H (idempotent i)))
  inversion : H →ₐ[k] H
  inversion_eq : inversion.toLinearMap = HopfAlgebra.antipode (R := k)

end Presentation

namespace ComponentHopfPresentation

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] (P : ComponentHopfPresentation k H)

def hopf : HopfAlgebra k (P.Index → k) :=
  letI := P.index_finite
  componentScalarHopf P.idempotent P.complete P.connected P.inversion P.inversion_eq

def inclusion : (P.Index → k) →ₐ[k] H :=
  letI := P.index_finite
  componentScalarInclusion P.idempotent P.complete

theorem injective : Function.Injective P.inclusion :=
  letI := P.index_finite
  componentScalarInclusion_injective P.idempotent P.complete P.connected

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
theorem finite : Module.Finite k (P.Index → k) :=
  letI := P.index_finite
  inferInstance

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
theorem etale : Algebra.Etale k (P.Index → k) := by
  letI := P.index_finite
  letI : Algebra.FormallyEtale k k := (algebraEtale_self k).formallyEtale
  letI : Algebra.FinitePresentation k (P.Index → k) :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := P.Index → k)).mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

theorem comul (x : P.Index → k) :
    letI := P.hopf
    Algebra.TensorProduct.map (S := k) P.inclusion P.inclusion (Bialgebra.comulAlgHom k (P.Index → k) x) =
      Bialgebra.comulAlgHom k H (P.inclusion x) :=
  letI := P.index_finite
  componentScalarInclusion_comul P.idempotent P.complete P.connected P.inversion P.inversion_eq x

theorem counit (x : P.Index → k) :
    letI := P.hopf
    Bialgebra.counitAlgHom k H (P.inclusion x) = Bialgebra.counitAlgHom k (P.Index → k) x := rfl

theorem antipode (x : P.Index → k) :
    letI := P.hopf
    P.inclusion (HopfAlgebra.antipode (R := k) x) = HopfAlgebra.antipode (R := k) (P.inclusion x) :=
  letI := P.index_finite
  componentScalarInclusion_antipode P.idempotent P.complete P.connected P.inversion P.inversion_eq x

end ComponentHopfPresentation

namespace ComponentHopfPresentation

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  (P : ComponentHopfPresentation k H)

/-- The counit selects a unique connected component. -/
theorem exists_identityIndex :
    ∃! i : P.Index, Bialgebra.counitAlgHom k H (P.idempotent i) = 1 := by
  letI := P.index_finite
  let ε := Bialgebra.counitAlgHom k H
  have hSome : ∃ i, ε (P.idempotent i) ≠ 0 := by
    by_contra! h
    have hOne := congrArg ε P.complete.complete
    simp only [map_sum, map_one, h, Finset.sum_const_zero, zero_ne_one] at hOne
  obtain ⟨i, hi⟩ := hSome
  have hi1 : ε (P.idempotent i) = 1 :=
    (IsIdempotentElem.iff_eq_zero_or_one.mp ((P.complete.idem i).map ε)).resolve_left hi
  refine ⟨i, hi1, fun j hj => ?_⟩
  by_contra hjne
  change ε (P.idempotent j) = 1 at hj
  have hzero := congrArg ε (P.complete.ortho hjne)
  rw [map_mul, map_zero, hj, hi1, mul_one] at hzero
  exact one_ne_zero hzero

/-- The identity component is the one containing the counit point. -/
def identityIndex : P.Index := Classical.choose P.exists_identityIndex.exists

theorem identityIndex_counit : Bialgebra.counitAlgHom k H (P.idempotent P.identityIndex) = 1 :=
  Classical.choose_spec P.exists_identityIndex.exists

/-- Coordinate ring of the identity component. -/
abbrev IdentityComponent := QuotientComponent H (P.idempotent P.identityIndex)

theorem identityComponent_connected : ConnectedSpace (PrimeSpectrum P.IdentityComponent) :=
  P.connected P.identityIndex

/-- Restrict a coordinate function to the identity component. -/
def identityQuotient : H →ₐ[k] P.IdentityComponent :=
  componentQuotient (k := k) P.idempotent P.identityIndex

/-- Component scalars restrict to the constant on the identity component. -/
theorem identityQuotient_inclusion (x : P.Index → k) :
    P.identityQuotient (P.inclusion x) = algebraMap k P.IdentityComponent (x P.identityIndex) :=
  letI := P.index_finite
  componentQuotient_inclusion P.idempotent P.complete P.identityIndex x

theorem identityQuotient_surjective : Function.Surjective P.identityQuotient :=
  Ideal.Quotient.mk_surjective

private theorem identityCounit_kills :
    Ideal.span {1 - P.idempotent P.identityIndex} ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change Bialgebra.counitAlgHom k H (1 - P.idempotent P.identityIndex) = 0
  rw [map_sub, map_one, P.identityIndex_counit, sub_self]

/-- The counit factors through the identity component quotient. -/
def identityCounit : P.IdentityComponent →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom k H) P.identityCounit_kills

@[simp] theorem identityCounit_comp_quotient :
    P.identityCounit.comp P.identityQuotient = Bialgebra.counitAlgHom k H :=
  Ideal.Quotient.liftₐ_comp _ _ _

end ComponentHopfPresentation

/-- A finite-type commutative Hopf algebra over an algebraically closed
field has the finite étale sub-Hopf algebra of its connected components. -/
theorem nonempty_componentHopfPresentation {k H : Type u} [Field k] [IsAlgClosed k]
    [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (S : H →ₐ[k] H) (hS : S.toLinearMap = HopfAlgebra.antipode (R := k)) :
    Nonempty (ComponentHopfPresentation k H) := by
  letI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨ι, hι, e, he, hc⟩ := exists_connected_component_idempotents H
  exact ⟨⟨ι, hι, e, he, hc, S, hS⟩⟩

section OrdinaryPV

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

local instance : CommRing (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).toCommRing
local instance : Algebra (LaurentPolynomial K) (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).algebra
local instance : Algebra K (ordinaryPVAlgebra A) := (ordinaryPVAlgebra A).algebra'

/-- The actual Picard–Vessiot group has a finite étale component algebra.
Its antipode is the tensor flip from the Picard–Vessiot construction. -/
theorem ordinaryPV_componentHopf :
    letI := ordinaryPVHopf A
    Nonempty (ComponentHopfPresentation K (ordinaryPVGroup A)) := by
  letI := ordinaryPVHopf A
  letI := ordinaryPVGroup_finiteType A
  exact nonempty_componentHopfPresentation
    (pvConstantFlip laurentDerivation (ordinaryPVDerivation A) (ordinaryPVDerivation_base A)) rfl

end OrdinaryPV

end WideE
