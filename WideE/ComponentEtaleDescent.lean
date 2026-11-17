import WideE.ComponentTorsorQuotient
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! Faithfully flat descent of the square-zero lifting property. -/

noncomputable section

open scoped TensorProduct

namespace WideE

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

set_option maxHeartbeats 750000

universe u

section Equalizer

variable {R S D : Type*} [CommRing R] [CommRing S] [CommRing D]
  [Algebra R S] [Algebra R D]

private theorem includeRight_injective [Module.FaithfullyFlat R S] :
    Function.Injective (Algebra.TensorProduct.includeRight : D →ₐ[R] S ⊗[R] D) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective D

/-- An element of a faithfully flat scalar extension comes from the original
algebra if its two images after extending scalars again agree. -/
theorem exists_includeRight_of_equalizer [Module.FaithfullyFlat R S] (x : S ⊗[R] D)
    (h : Algebra.TensorProduct.map (AlgHom.id R S)
      (Algebra.TensorProduct.includeRight : D →ₐ[R] S ⊗[R] D) x =
        Algebra.TensorProduct.includeRight x) :
    ∃ d : D, Algebra.TensorProduct.includeRight d = x := by
  let i := (Algebra.TensorProduct.includeRight : D →ₐ[R] S ⊗[R] D).toLinearMap
  let p := (LinearMap.range i).mkQ
  have hzero : p.lTensor S (Algebra.TensorProduct.map (AlgHom.id R S)
      (Algebra.TensorProduct.includeRight : D →ₐ[R] S ⊗[R] D) x) = 0 := by
    clear h
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    | tmul s d =>
      change p.lTensor S (s ⊗ₜ[R] i d) = 0
      rw [LinearMap.lTensor_tmul]
      have hz : p (i d) = 0 :=
        (Submodule.Quotient.mk_eq_zero (LinearMap.range i)).mpr (LinearMap.mem_range_self i d)
      rw [hz, TensorProduct.tmul_zero]
  have hx : p x = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S)
      ((S ⊗[R] D) ⧸ LinearMap.range i)
    rw [map_zero]
    change (1 : S) ⊗ₜ[R] p x = 0
    change p.lTensor S (Algebra.TensorProduct.includeRight x) = 0
    rw [← h]
    exact hzero
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range i)).mp hx

end Equalizer

section Lifting

variable {R A D E : Type u} [CommRing R] [CommRing A] [CommRing D] [CommRing E]
  [Algebra R A] [Algebra R D] [Algebra R E]

private theorem squareZeroLift_bijective [Algebra.FormallyEtale R A]
    (q : D →ₐ[R] E) (hq : Function.Surjective q) (hzero : (RingHom.ker q)^2 = ⊥) :
    Function.Bijective (q.comp : (A →ₐ[R] D) → A →ₐ[R] E) := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hq
  have h' : (q.comp : (A →ₐ[R] D) → A →ₐ[R] E) =
      (e.toAlgHom.comp : (A →ₐ[R] D ⧸ RingHom.ker q) → A →ₐ[R] E) ∘
        (Ideal.Quotient.mkₐ R (RingHom.ker q)).comp := by
    funext f
    apply AlgHom.ext
    intro a
    rfl
  rw [h']
  refine Function.Bijective.comp ?_ (Algebra.FormallyEtale.comp_bijective _ hzero)
  constructor
  · intro f g h
    apply AlgHom.ext
    intro a
    exact e.injective (congrArg (fun i : A →ₐ[R] E => i a) h)
  · intro f
    exact ⟨e.symm.toAlgHom.comp f, AlgHom.ext (fun a => e.apply_symm_apply (f a))⟩

private theorem tensor_map_surjective {S : Type*} [CommRing S] [Algebra R S]
    (q : D →ₐ[R] E) (hq : Function.Surjective q) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id R S) q) :=
  LinearMap.lTensor_surjective S hq

private theorem tensor_map_ker_squareZero {S : Type*} [CommRing S] [Algebra R S]
    (q : D →ₐ[R] E) (hq : Function.Surjective q) (hzero : (RingHom.ker q)^2 = ⊥) :
    (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) q))^2 = ⊥ := by
  rw [Algebra.TensorProduct.lTensor_ker q hq, ← Ideal.map_pow, hzero, Ideal.map_bot]

end Lifting

section FaithfullyFlat

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "ι" => Algebra.TensorProduct.includeRight
local notation "M" => Algebra.TensorProduct.map

/-- The unique square-zero lift over a faithfully flat cover descends to
the original algebra. -/
theorem formallyEtale_of_faithfullyFlat_tensor (S : Type u) [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [Algebra.FormallyEtale S (S ⊗[R] A)] :
    Algebra.FormallyEtale R A := by
  constructor
  intro D _ _ I hI
  let L := S ⊗[R] D
  let L' := S ⊗[R] (D ⧸ I)
  let q := Ideal.Quotient.mkₐ R I
  let q₁ : L →ₐ[R] L' := M (AlgHom.id R S) q
  let qS₁ : L →ₐ[S] L' := M (AlgHom.id S S) q
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hqI : (RingHom.ker q)^2 = ⊥ := by
    change RingHom.ker (Ideal.Quotient.mk I) ^ 2 = ⊥
    rw [Ideal.mk_ker, hI]
  have hq₁ : Function.Surjective q₁ := tensor_map_surjective q hq
  have hq₁I : (RingHom.ker q₁)^2 = ⊥ := tensor_map_ker_squareZero q hq hqI
  let lift₁ (f : A →ₐ[R] D) : (S ⊗[R] A) →ₐ[S] L := M (AlgHom.id S S) f
  have inj := (squareZeroLift_bijective (A := S ⊗[R] A) qS₁ hq₁ hq₁I).1
  constructor
  · intro f g h
    have h' : qS₁.comp (lift₁ f) = qS₁.comp (lift₁ g) := by
      change q.comp f = q.comp g at h
      change (M (AlgHom.id S S) q).comp (M (AlgHom.id S S) f) =
        (M (AlgHom.id S S) q).comp (M (AlgHom.id S S) g)
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, h]
    apply AlgHom.ext
    intro a
    apply includeRight_injective (R := R) (S := S)
    exact congrArg (fun l : (S ⊗[R] A) →ₐ[S] L => l (ι a)) (inj h')
  · intro f
    obtain ⟨g, hg⟩ := (squareZeroLift_bijective (A := S ⊗[R] A) qS₁ hq₁ hq₁I).2
      (M (AlgHom.id S S) f)
    let g₀ : A →ₐ[R] L := (g.restrictScalars R).comp ι
    have hg₀ (a : A) : q₁ (g₀ a) = ι (f a) :=
      congrArg (fun l : (S ⊗[R] A) →ₐ[S] L' => l (ι a)) hg
    let U := S ⊗[R] L
    let U' := S ⊗[R] L'
    let q₂ : U →ₐ[S] U' := M (AlgHom.id S S) q₁
    have hq₂ : Function.Surjective q₂ := tensor_map_surjective q₁ hq₁
    have hq₂I : (RingHom.ker q₂)^2 = ⊥ := tensor_map_ker_squareZero q₁ hq₁ hq₁I
    let d₁ : L →ₐ[R] U := M (AlgHom.id R S) ι
    let d₂ : L →ₐ[R] U := ι
    let m₁ : (S ⊗[R] A) →ₐ[S] U :=
      Algebra.TensorProduct.lift (Algebra.ofId S U) (d₁.comp g₀) (fun _ _ => Commute.all _ _)
    let m₂ : (S ⊗[R] A) →ₐ[S] U :=
      Algebra.TensorProduct.lift (Algebra.ofId S U) (d₂.comp g₀) (fun _ _ => Commute.all _ _)
    have h₁ : (q₂.restrictScalars R).comp d₁ =
        (M (AlgHom.id R S) ι).comp q₁ := by
      apply Algebra.TensorProduct.ext'
      intro s d
      rfl
    have h₂ : (q₂.restrictScalars R).comp d₂ = (ι).comp q₁ := by
      apply AlgHom.ext
      intro l
      change M (AlgHom.id S S) q₁ (1 ⊗ₜ[R] l) = 1 ⊗ₜ[R] q₁ l
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hm : q₂.comp m₁ = q₂.comp m₂ := by
      apply Algebra.TensorProduct.ext'
      intro s a
      simp only [m₁, m₂, AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_mul]
      congr 1
      have h₁a := congrArg (fun l : L →ₐ[R] U' => l (g₀ a)) h₁
      have h₂a := congrArg (fun l : L →ₐ[R] U' => l (g₀ a)) h₂
      change q₂ (d₁ (g₀ a)) = M (AlgHom.id R S) ι (q₁ (g₀ a)) at h₁a
      change q₂ (d₂ (g₀ a)) = ι (q₁ (g₀ a)) at h₂a
      rw [h₁a, h₂a, hg₀]
      rfl
    have hdesc (a : A) : ∃ d : D, ι d = g₀ a := by
      apply exists_includeRight_of_equalizer
      have h := congrArg (fun l : (S ⊗[R] A) →ₐ[S] U => l (ι a))
        ((squareZeroLift_bijective (A := S ⊗[R] A) q₂ hq₂ hq₂I).1 hm)
      simpa only [m₁, m₂, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply] using h
    let d (a : A) := Classical.choose (hdesc a)
    have hd (a : A) : ι (d a) = g₀ a := Classical.choose_spec (hdesc a)
    let dHom : A →ₐ[R] D :=
      { toFun := d
        map_zero' := by
          apply includeRight_injective (R := R) (S := S)
          rw [hd, map_zero, map_zero]
        map_one' := by
          apply includeRight_injective (R := R) (S := S)
          rw [hd, map_one, map_one]
        map_add' := fun a b => by
          apply includeRight_injective (R := R) (S := S)
          rw [hd, map_add g₀, map_add ι, hd, hd]
        map_mul' := fun a b => by
          apply includeRight_injective (R := R) (S := S)
          rw [hd, map_mul g₀, map_mul ι, hd, hd]
        commutes' := fun r => by
          apply includeRight_injective (R := R) (S := S)
          rw [hd, AlgHom.commutes, AlgHom.commutes] }
    refine ⟨dHom, AlgHom.ext (fun a => ?_)⟩
    apply includeRight_injective (R := R) (S := S)
    change ι (q (d a)) = ι (f a)
    calc
      _ = q₁ (ι (d a)) := by
        change (1 : S) ⊗ₜ[R] q (d a) = M (AlgHom.id R S) q (1 ⊗ₜ[R] d a)
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      _ = q₁ (g₀ a) := by rw [hd]
      _ = _ := hg₀ a

end FaithfullyFlat

section Components

variable {k B S H : Type u} [Field k] [IsAlgClosed k] [CommRing B] [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k S] [Algebra B S] [IsScalarTower k B S] [HopfAlgebra k H]
  (T : AffineHopfTorsor k B S H) (G : ComponentHopfPresentation k H)

/-- The component quotient is finite étale over a Noetherian base, as can
be checked after pulling back along the faithfully flat torsor. -/
theorem componentTorsorQuotient_etale [IsNoetherianRing B] :
    Algebra.Etale B (componentTorsorQuotient T G) := by
  letI := T.faithfullyFlat
  letI := componentTorsorQuotient_finite T G
  letI := componentTorsorQuotient_etale_after_baseChange T G
  letI : Algebra.FormallyEtale B (componentTorsorQuotient T G) :=
    formallyEtale_of_faithfullyFlat_tensor S
  exact ⟨inferInstance, (Algebra.FinitePresentation.of_finiteType (R := B) (A := componentTorsorQuotient T G)).mp inferInstance⟩

end Components

end WideE
