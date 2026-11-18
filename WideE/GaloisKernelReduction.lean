import WideE.HopfPointGroup
import WideE.HopfQuotient
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! Reduction of nonabelian Galois cocycles to the kernel of a faithfully flat group map. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section Points

variable {k Q H A : Type*} [CommRing k] [CommRing Q] [CommRing H] [CommRing A]
  [HopfAlgebra k Q] [HopfAlgebra k H] [Algebra k A]

/-- A map of group coordinates induces the contravariant homomorphism of point groups. -/
def hopfPointPrecompose (j : Q →ₐc[k] H) :
    letI := hopfPointGroup (k := k) (H := H) (A := A)
    letI := hopfPointGroup (k := k) (H := Q) (A := A)
    (H →ₐ[k] A) →* (Q →ₐ[k] A) := by
  letI := hopfPointGroup (k := k) (H := H) (A := A)
  letI := hopfPointGroup (k := k) (H := Q) (A := A)
  let f : Q →ₐ[k] H := j
  refine { toFun := fun p => p.comp f, map_one' := ?_, map_mul' := ?_ }
  · apply AlgHom.ext
    intro a
    exact congrArg (algebraMap k A)
      (DFunLike.congr_fun (BialgHomClass.counitAlgHom_comp j) a)
  · intro p q
    have h (z : Q ⊗[k] Q) :
        tensorPoint p q (Algebra.TensorProduct.map f f z) = tensorPoint (p.comp f) (q.comp f) z := by
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y => simp only [Algebra.TensorProduct.map_tmul, tensorPoint_tmul, AlgHom.comp_apply]
    apply AlgHom.ext
    intro a
    have hΔ := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom j) a
    change Algebra.TensorProduct.map f f (Bialgebra.comulAlgHom k Q a) =
      Bialgebra.comulAlgHom k H (f a) at hΔ
    change tensorPoint p q (Bialgebra.comulAlgHom k H (f a)) =
      tensorPoint (p.comp f) (q.comp f) (Bialgebra.comulAlgHom k Q a)
    rw [← hΔ, h]

@[simp] theorem hopfPointPrecompose_apply (j : Q →ₐc[k] H) (p : H →ₐ[k] A) :
    hopfPointPrecompose j p = p.comp (j : Q →ₐ[k] H) := rfl

theorem hopfPointPrecompose_injective (j : Q →ₐc[k] H) (hj : Function.Surjective j) :
    Function.Injective (hopfPointPrecompose (A := A) j) := by
  intro p q hpq
  apply AlgHom.ext
  intro a
  obtain ⟨x, rfl⟩ := hj a
  exact DFunLike.congr_fun hpq x

end Points

section Cocycles

variable {k F L Q H : Type*} [CommRing k] [Field F] [Field L] [CommRing Q] [CommRing H]
  [HopfAlgebra k Q] [HopfAlgebra k H] [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]

/-- The image cocycle obtained by evaluating its points on the quotient coordinates. -/
def precomposeHopfPointCocycle (j : Q →ₐc[k] H) (c : (L ≃ₐ[F] L) → H →ₐ[k] L) :
    (L ≃ₐ[F] L) → Q →ₐ[k] L := fun σ => hopfPointPrecompose j (c σ)

theorem IsHopfPointCocycle.precompose {c : (L ≃ₐ[F] L) → H →ₐ[k] L}
    (hc : IsHopfPointCocycle c) (j : Q →ₐc[k] H) :
    IsHopfPointCocycle (precomposeHopfPointCocycle j c) := by
  letI := hopfPointGroup (k := k) (H := H) (A := L)
  letI := hopfPointGroup (k := k) (H := Q) (A := L)
  let f := hopfPointPrecompose (A := L) j
  constructor
  · change f (c 1) = 1
    rw [show c 1 = 1 from hc.1, map_one]
  · intro σ τ
    let s := σ.toAlgHom.restrictScalars k
    change f (c (σ * τ)) = f (c σ) * f (s.comp (c τ))
    rw [← map_mul]
    exact congrArg f (hc.2 σ τ)

theorem IsHopfPointCoboundary.precompose {c : (L ≃ₐ[F] L) → H →ₐ[k] L}
    (hc : IsHopfPointCoboundary c) (j : Q →ₐc[k] H) :
    IsHopfPointCoboundary (precomposeHopfPointCocycle j c) := by
  letI := hopfPointGroup (k := k) (H := H) (A := L)
  letI := hopfPointGroup (k := k) (H := Q) (A := L)
  let f := hopfPointPrecompose (A := L) j
  obtain ⟨b, hb⟩ := hc
  refine ⟨f b, fun σ => ?_⟩
  change f (c σ) * f ((σ.toAlgHom.restrictScalars k).comp b) = f b
  rw [← map_mul]
  exact congrArg f (hb σ)

private def galoisHopfPointHom (σ : L ≃ₐ[F] L) :
    letI := hopfPointGroup (k := k) (H := H) (A := L)
    (H →ₐ[k] L) →* (H →ₐ[k] L) := by
  letI := hopfPointGroup (k := k) (H := H) (A := L)
  let f := σ.toAlgHom.restrictScalars k
  exact
    { toFun := fun p => f.comp p
      map_one' := hopfPointOne_postcompose f
      map_mul' := hopfPointMul_postcompose f }

/-- Change the chosen point by `b` in the right action convention. -/
def twistHopfPointCocycle (c : (L ≃ₐ[F] L) → H →ₐ[k] L) (b : H →ₐ[k] L) (σ : L ≃ₐ[F] L) :
    H →ₐ[k] L :=
  letI := hopfPointGroup (k := k) (H := H) (A := L)
  b⁻¹ * c σ * galoisHopfPointHom σ b

theorem IsHopfPointCocycle.twist {c : (L ≃ₐ[F] L) → H →ₐ[k] L}
    (hc : IsHopfPointCocycle c) (b : H →ₐ[k] L) :
    IsHopfPointCocycle (twistHopfPointCocycle c b) := by
  letI := hopfPointGroup (k := k) (H := H) (A := L)
  let ρ (σ : L ≃ₐ[F] L) := galoisHopfPointHom (k := k) (H := H) σ
  constructor
  · change b⁻¹ * c 1 * ρ 1 b = 1
    rw [show c 1 = 1 from hc.1, show ρ 1 b = b from rfl, mul_one, inv_mul_cancel]
  · intro σ τ
    change b⁻¹ * c (σ * τ) * ρ (σ * τ) b =
      (b⁻¹ * c σ * ρ σ b) * ρ σ (b⁻¹ * c τ * ρ τ b)
    have hcomp : ρ (σ * τ) b = ρ σ (ρ τ b) := rfl
    have hc' : c (σ * τ) = c σ * ρ σ (c τ) := hc.2 σ τ
    rw [hcomp, hc', map_mul, map_mul, map_inv]
    simp [mul_assoc]

theorem isHopfPointCoboundary_of_twist {c : (L ≃ₐ[F] L) → H →ₐ[k] L} (b : H →ₐ[k] L)
    (hc : IsHopfPointCoboundary (twistHopfPointCocycle c b)) : IsHopfPointCoboundary c := by
  letI := hopfPointGroup (k := k) (H := H) (A := L)
  obtain ⟨a, ha⟩ := hc
  refine ⟨b * a, fun σ => ?_⟩
  let ρ := galoisHopfPointHom (k := k) (H := H) σ
  have h : (b⁻¹ * c σ * ρ b) * ρ a = a := ha σ
  change c σ * ρ (b * a) = b * a
  rw [map_mul]
  simpa [mul_assoc] using congrArg (fun g => b * g) h

private theorem precompose_twistHopfPointCocycle (j : Q →ₐc[k] H)
    (c : (L ≃ₐ[F] L) → H →ₐ[k] L) (b : H →ₐ[k] L) (σ : L ≃ₐ[F] L) :
    hopfPointPrecompose j (twistHopfPointCocycle c b σ) =
      twistHopfPointCocycle (precomposeHopfPointCocycle j c) (hopfPointPrecompose j b) σ := by
  letI := hopfPointGroup (k := k) (H := H) (A := L)
  letI := hopfPointGroup (k := k) (H := Q) (A := L)
  let f := hopfPointPrecompose (A := L) j
  let ρH := galoisHopfPointHom (k := k) (H := H) σ
  let ρQ := galoisHopfPointHom (k := k) (H := Q) σ
  change f (b⁻¹ * c σ * ρH b) = (f b)⁻¹ * f (c σ) * ρQ (f b)
  rw [map_mul, map_mul, map_inv]
  rfl

private theorem twistHopfPointCocycle_eq_one_of_witness
    (c : (L ≃ₐ[F] L) → H →ₐ[k] L) (b : H →ₐ[k] L) (σ : L ≃ₐ[F] L)
    (h : hopfPointMul (c σ) ((σ.toAlgHom.restrictScalars k).comp b) = b) :
    twistHopfPointCocycle c b σ = hopfPointOne := by
  letI := hopfPointGroup (k := k) (H := H) (A := L)
  let ρ := galoisHopfPointHom (k := k) (H := H) σ
  change b⁻¹ * c σ * ρ b = 1
  rw [mul_assoc, show c σ * ρ b = b from h, inv_mul_cancel]

end Cocycles

section InflationNaturality

variable {k F E L Q H : Type*} [CommRing k] [Field F] [Field E] [Field L]
  [CommRing Q] [CommRing H] [HopfAlgebra k Q] [HopfAlgebra k H]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower F E L] [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [Normal F E]

omit [Algebra k F] [IsScalarTower k F E] [IsScalarTower k F L] in
private theorem precompose_inflateHopfPointCocycle (j : Q →ₐc[k] H)
    (c : (E ≃ₐ[F] E) → H →ₐ[k] E) :
    precomposeHopfPointCocycle j (inflateHopfPointCocycle (L := L) c) =
      inflateHopfPointCocycle (L := L) (precomposeHopfPointCocycle j c) :=
  funext fun _ => AlgHom.ext fun _ => rfl

private theorem hopfPointCoboundaryWitness_inflate
    (c : (E ≃ₐ[F] E) → H →ₐ[k] E) (b : H →ₐ[k] E)
    (hb : ∀ τ : E ≃ₐ[F] E, hopfPointMul (c τ) ((τ.toAlgHom.restrictScalars k).comp b) = b)
    (σ : L ≃ₐ[F] L) :
    let b' := (IsScalarTower.toAlgHom k E L).comp b
    hopfPointMul (inflateHopfPointCocycle c σ) ((σ.toAlgHom.restrictScalars k).comp b') = b' := by
  let i := IsScalarTower.toAlgHom k E L
  let τ := AlgEquiv.restrictNormalHom E σ
  have h : (σ.toAlgHom.restrictScalars k).comp (i.comp b) =
      i.comp ((τ.toAlgHom.restrictScalars k).comp b) :=
    AlgHom.ext fun x => (σ.restrictNormal_commutes E (b x)).symm
  change hopfPointMul (i.comp (c τ)) ((σ.toAlgHom.restrictScalars k).comp (i.comp b)) = i.comp b
  rw [h, ← hopfPointMul_postcompose, hb τ]

/-- A trivial quotient cocycle after Galois enlargement already has a
coboundary at the original field of definition. -/
theorem isHopfPointQuotientCoboundary_inflate_iff [IsGalois F L] (j : Q →ₐc[k] H)
    {c : (E ≃ₐ[F] E) → H →ₐ[k] E} (hc : IsHopfPointCocycle c) :
    IsHopfPointCoboundary (precomposeHopfPointCocycle j (inflateHopfPointCocycle (L := L) c)) ↔
      IsHopfPointCoboundary (precomposeHopfPointCocycle j c) := by
  rw [precompose_inflateHopfPointCocycle]
  exact isHopfPointCoboundary_inflate_iff (hc.precompose j)

end InflationNaturality

section FiniteGaloisPoints

variable {F : Type*} [Field F] [CharZero F]

/-- A point of a finite-type algebra over a finite Galois subfield can be
chosen over a finite Galois enlargement with the prescribed scalar inclusion. -/
theorem exists_finiteGalois_point_over_intermediate
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (S : Type*)
    [CommRing S] [Algebra E S] [Algebra.FiniteType E S] [Nontrivial S] :
    ∃ (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (hEL : E ≤ L),
      letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
      Nonempty (S →ₐ[E] L) := by
  letI : Algebra F S := ((algebraMap E S).comp (algebraMap F E)).toAlgebra
  letI : IsScalarTower F E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.FiniteType F S := Algebra.FiniteType.trans (S := E) inferInstance inferInstance
  obtain ⟨L₀, hFinite, hGalois, ⟨p⟩⟩ := exists_finiteGalois_point (K := F) (S := S)
  letI := hFinite
  letI := hGalois
  let L := FiniteGaloisIntermediateField.mk L₀
  let f : E →ₐ[F] L := p.comp (IsScalarTower.toAlgHom F E S)
  let g : E →ₐ[F] AlgebraicClosure F := L.toIntermediateField.val.comp f
  let u := g.restrictNormal' E
  have hg (x : E) : ((u x : E) : AlgebraicClosure F) = g x :=
    g.restrictNormal_commutes E x
  have hEL : E ≤ L := by
    change E.toIntermediateField ≤ L.toIntermediateField
    intro z hz
    let x : E := ⟨z, hz⟩
    have hx : g (u.symm x) ∈ L.toIntermediateField := (f (u.symm x)).property
    rw [← hg, AlgEquiv.apply_symm_apply] at hx
    exact hx
  let i := IntermediateField.inclusion hEL
  letI : Algebra E L := i.toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algHom i
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) L u.symm
  have hf (x : E) : f x = i (u x) := Subtype.ext (hg x).symm
  refine ⟨L, hEL, ⟨{ toRingHom := (τ.toAlgHom.comp p).toRingHom, commutes' := ?_ }⟩⟩
  intro x
  change τ (f x) = algebraMap E L x
  rw [hf]
  change τ (algebraMap E L (u x)) = algebraMap E L x
  calc
    _ = algebraMap E L (AlgEquiv.restrictNormalHom E τ (u x)) :=
      (τ.restrictNormal_commutes E (u x)).symm
    _ = _ := by rw [hτ, AlgEquiv.symm_apply_apply]

end FiniteGaloisPoints

section KernelIdeal

variable {k Q H : Type*} [CommRing k] [CommRing Q] [CommRing H]
  [HopfAlgebra k Q] [HopfAlgebra k H]

/-- The coordinate ideal of the fiber of a group map over the identity. -/
def hopfKernelIdeal (j : Q →ₐc[k] H) : Ideal H :=
  (RingHom.ker (Bialgebra.counitAlgHom k Q).toRingHom).map (j : Q →ₐ[k] H).toRingHom

/-- The canonical map to the identity fiber restricts to the quotient counit. -/
theorem hopfKernel_mk_precompose (j : Q →ₐc[k] H) :
    hopfPointPrecompose j (Ideal.Quotient.mkₐ k (hopfKernelIdeal j)) = hopfPointOne := by
  let f : Q →ₐ[k] H := j
  let p := Ideal.Quotient.mkₐ k (hopfKernelIdeal j)
  let ε := Bialgebra.counitAlgHom k Q
  apply AlgHom.ext
  intro x
  have hx : x - algebraMap k Q (ε x) ∈ RingHom.ker ε.toRingHom := by
    change ε (x - algebraMap k Q (ε x)) = 0
    simp
  have hz : p (f (x - algebraMap k Q (ε x))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f.toRingHom hx)
  rw [map_sub, map_sub, f.commutes, p.commutes, sub_eq_zero] at hz
  exact hz

/-- The ideal of the identity fiber carries the canonical closed kernel group. -/
theorem hopfKernelIdeal_isHopf (j : Q →ₐc[k] H) : IsHopfIdeal k (hopfKernelIdeal j) := by
  let f : Q →ₐ[k] H := j
  let A := H ⧸ hopfKernelIdeal j
  let p : H →ₐ[k] A := Ideal.Quotient.mkₐ k (hopfKernelIdeal j)
  have hp : hopfPointPrecompose j p = hopfPointOne := hopfKernel_mk_precompose j
  refine ⟨?_, ?_, ?_⟩ <;> change Ideal.map f.toRingHom _ ≤ _ <;> rw [Ideal.map_le_iff_le_comap]
  · intro x hx
    change Bialgebra.counitAlgHom k Q x = 0 at hx
    let l : A →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.includeLeft
    let r : A →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.includeRight
    letI := hopfPointGroup (k := k) (H := H) (A := A ⊗[k] A)
    letI := hopfPointGroup (k := k) (H := Q) (A := A ⊗[k] A)
    have hl : hopfPointPrecompose j (l.comp p) = hopfPointOne :=
      (congrArg (fun u => l.comp u) hp).trans (hopfPointOne_postcompose l)
    have hr : hopfPointPrecompose j (r.comp p) = hopfPointOne :=
      (congrArg (fun u => r.comp u) hp).trans (hopfPointOne_postcompose r)
    have hm := map_mul (hopfPointPrecompose (A := A ⊗[k] A) j) (l.comp p) (r.comp p)
    change hopfPointPrecompose j (hopfPointMul (l.comp p) (r.comp p)) =
      hopfPointMul (hopfPointPrecompose j (l.comp p)) (hopfPointPrecompose j (r.comp p)) at hm
    rw [hl, hr, hopfPointMul_one_left] at hm
    have hTensor : tensorPoint (l.comp p) (r.comp p) = Algebra.TensorProduct.map p p := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp only [tensorPoint_tmul, AlgHom.comp_apply, l, r, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul, Algebra.TensorProduct.map_tmul]
    have h := DFunLike.congr_fun hm x
    change tensorPoint (l.comp p) (r.comp p) (Bialgebra.comulAlgHom k H (f x)) =
      algebraMap k (A ⊗[k] A) (Bialgebra.counitAlgHom k Q x) at h
    rw [hTensor, hx, map_zero] at h
    exact h
  · intro x hx
    change Bialgebra.counitAlgHom k H (f x) = 0
    exact (DFunLike.congr_fun (BialgHomClass.counitAlgHom_comp j) x).trans hx
  · intro x hx
    change Bialgebra.counitAlgHom k Q x = 0 at hx
    letI := hopfPointGroup (k := k) (H := H) (A := A)
    letI := hopfPointGroup (k := k) (H := Q) (A := A)
    have hi := map_inv (hopfPointPrecompose (A := A) j) p
    rw [hp, show (hopfPointOne : Q →ₐ[k] A)⁻¹ = hopfPointOne from inv_one] at hi
    have h := DFunLike.congr_fun hi x
    change p (hopfAntipodeAlgHom k H (f x)) = algebraMap k A (Bialgebra.counitAlgHom k Q x) at h
    rwa [hx, map_zero] at h

end KernelIdeal

section KernelFactorization

variable {k Q H J A : Type*} [CommRing k] [CommRing Q] [CommRing H] [CommRing J] [CommRing A]
  [HopfAlgebra k Q] [HopfAlgebra k H] [HopfAlgebra k J] [Algebra k A]

/-- A point above the identity factors through the kernel quotient defined by
the extended augmentation ideal. -/
theorem exists_hopfPoint_in_kernel_of_trivial_image (j : Q →ₐc[k] H) (π : H →ₐc[k] J)
    (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : H →ₐ[k] J).toRingHom =
      (RingHom.ker (Bialgebra.counitAlgHom k Q).toRingHom).map (j : Q →ₐ[k] H).toRingHom)
    (b : H →ₐ[k] A) (hb : hopfPointPrecompose j b = hopfPointOne) :
    ∃ a : J →ₐ[k] A, hopfPointPrecompose π a = b := by
  let f : H →ₐ[k] J := π
  let I := RingHom.ker f.toRingHom
  have hI : I ≤ RingHom.ker b.toRingHom := by
    change RingHom.ker (π : H →ₐ[k] J).toRingHom ≤ RingHom.ker b.toRingHom
    rw [hker, Ideal.map_le_iff_le_comap]
    intro x hx
    change b (j x) = 0
    change Bialgebra.counitAlgHom k Q x = 0 at hx
    have h := DFunLike.congr_fun hb x
    change b (j x) = algebraMap k A (Bialgebra.counitAlgHom k Q x) at h
    rwa [hx, map_zero] at h
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := f) hπ
  let a := (Ideal.Quotient.liftₐ I b hI).comp e.symm.toAlgHom
  refine ⟨a, AlgHom.ext fun x => ?_⟩
  have h : e (Ideal.Quotient.mk I x) = f x := rfl
  change Ideal.Quotient.liftₐ I b hI (e.symm (f x)) = b x
  rw [← h, AlgEquiv.symm_apply_apply]
  rfl

variable {F L : Type*} [Field F] [Field L] [Algebra k F] [Algebra k L] [Algebra F L]
  [IsScalarTower k F L]

/-- A cocycle whose quotient values are the identity factors as a genuine
cocycle of the kernel group. -/
theorem exists_kernelHopfPointCocycle (j : Q →ₐc[k] H) (π : H →ₐc[k] J)
    (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : H →ₐ[k] J).toRingHom =
      (RingHom.ker (Bialgebra.counitAlgHom k Q).toRingHom).map (j : Q →ₐ[k] H).toRingHom)
    (c : (L ≃ₐ[F] L) → H →ₐ[k] L) (hc : IsHopfPointCocycle c)
    (hOne : ∀ σ, hopfPointPrecompose j (c σ) = hopfPointOne) :
    ∃ d : (L ≃ₐ[F] L) → J →ₐ[k] L, IsHopfPointCocycle d ∧ precomposeHopfPointCocycle π d = c := by
  classical
  choose d hd using fun σ => exists_hopfPoint_in_kernel_of_trivial_image j π hπ hker (c σ) (hOne σ)
  letI := hopfPointGroup (k := k) (H := H) (A := L)
  letI := hopfPointGroup (k := k) (H := J) (A := L)
  let f := hopfPointPrecompose (A := L) π
  have hf : Function.Injective f := hopfPointPrecompose_injective π hπ
  refine ⟨d, ⟨?_, ?_⟩, funext hd⟩
  · apply hf
    change f (d 1) = f 1
    rw [show f (d 1) = c 1 from hd 1, map_one]
    exact hc.1
  · intro σ τ
    apply hf
    let s := σ.toAlgHom.restrictScalars k
    change f (d (σ * τ)) = f (d σ * s.comp (d τ))
    rw [map_mul, show f (d (σ * τ)) = c (σ * τ) from hd (σ * τ), show f (d σ) = c σ from hd σ]
    change c (σ * τ) = c σ * s.comp (f (d τ))
    rw [show f (d τ) = c τ from hd τ]
    exact hc.2 σ τ

end KernelFactorization

section QuotientFibers

variable {k F Q H : Type*} [CommRing k] [Field F] [CharZero F] [Algebra k F]
  [CommRing Q] [CommRing H] [HopfAlgebra k Q] [HopfAlgebra k H] [Algebra.FiniteType k H]

omit [CharZero F] in
private theorem finiteGaloisInclusion_scalarTower
    {E L : FiniteGaloisIntermediateField F (AlgebraicClosure F)} (hEL : E ≤ L) :
    letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
    IsScalarTower k E L := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    ((IntermediateField.inclusion hEL).restrictScalars k).comp_algebraMap.symm

/-- A quotient point lifts over a finite Galois enlargement by taking a point
of its actual faithfully flat fiber. -/
theorem exists_liftHopfPoint_after_finiteGalois
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (j : Q →ₐc[k] H)
    (hj : letI : Algebra Q H := (j : Q →ₐ[k] H).toRingHom.toAlgebra; Module.FaithfullyFlat Q H)
    (q : Q →ₐ[k] E) :
    ∃ (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (hEL : E ≤ L) (b : H →ₐ[k] L),
      b.comp (j : Q →ₐ[k] H) = ((IntermediateField.inclusion hEL).restrictScalars k).comp q := by
  let f : Q →ₐ[k] H := j
  letI : Algebra Q H := f.toRingHom.toAlgebra
  letI : Algebra Q E := q.toRingHom.toAlgebra
  letI : IsScalarTower k Q H := IsScalarTower.of_algHom f
  letI : IsScalarTower k Q E := IsScalarTower.of_algHom q
  letI : Module.FaithfullyFlat Q H := hj
  let S := E ⊗[Q] H
  letI : Algebra E S := Algebra.TensorProduct.leftAlgebra
  letI : Algebra.FiniteType Q H := Algebra.FiniteType.of_restrictScalars_finiteType k Q H
  letI : Algebra.FiniteType E S := Algebra.FiniteType.baseChange (R := Q) E
  letI : Nontrivial S := ((TensorProduct.comm Q E H).symm.injective.comp
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := Q) (B := H) E)).nontrivial
  obtain ⟨L, hEL, ⟨p⟩⟩ := exists_finiteGalois_point_over_intermediate E S
  let i := IntermediateField.inclusion hEL
  letI : Algebra E L := i.toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algHom i
  letI : IsScalarTower k E L := finiteGaloisInclusion_scalarTower (k := k) hEL
  have hbal (x : Q) : (1 : E) ⊗ₜ[Q] f x = (q x) ⊗ₜ[Q] (1 : H) := by
    change (1 : E) ⊗ₜ[Q] algebraMap Q H x = algebraMap Q E x ⊗ₜ[Q] (1 : H)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (TensorProduct.smul_tmul x (1 : E) (1 : H)).symm
  let jH : H →ₐ[Q] S := Algebra.TensorProduct.includeRight
  let b : H →ₐ[k] L :=
    { toRingHom := p.toRingHom.comp jH.toRingHom
      commutes' := fun a => by
        change p ((1 : E) ⊗ₜ[Q] algebraMap k H a) = algebraMap k L a
        rw [← f.commutes, hbal, q.commutes]
        exact (p.commutes (algebraMap k E a)).trans (IsScalarTower.algebraMap_apply k E L a).symm }
  refine ⟨L, hEL, b, AlgHom.ext fun x => ?_⟩
  change p ((1 : E) ⊗ₜ[Q] f x) = i (q x)
  rw [hbal]
  exact p.commutes (q x)

variable {J : Type*} [CommRing J] [HopfAlgebra k J]

/-- Lift a prescribed quotient coboundary, twist the original cocycle,
and factor the twisted cocycle through the actual kernel. A kernel
coboundary then supplies a coboundary over the original field. -/
theorem exists_kernelCocycle_of_quotientCoboundary
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (j : Q →ₐc[k] H)
    (hj : letI : Algebra Q H := (j : Q →ₐ[k] H).toRingHom.toAlgebra; Module.FaithfullyFlat Q H)
    (π : H →ₐc[k] J) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : H →ₐ[k] J).toRingHom =
      (RingHom.ker (Bialgebra.counitAlgHom k Q).toRingHom).map (j : Q →ₐ[k] H).toRingHom)
    (c : (E ≃ₐ[F] E) → H →ₐ[k] E) (hc : IsHopfPointCocycle c)
    (q : Q →ₐ[k] E) (hq : ∀ σ : E ≃ₐ[F] E, hopfPointMul (precomposeHopfPointCocycle j c σ)
      ((σ.toAlgHom.restrictScalars k).comp q) = q) :
    ∃ (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (hEL : E ≤ L),
      letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
      letI : IsScalarTower F E L := IsScalarTower.of_algHom (IntermediateField.inclusion hEL)
      letI : IsScalarTower k E L := finiteGaloisInclusion_scalarTower (k := k) hEL
      ∃ (b : H →ₐ[k] L) (d : (L ≃ₐ[F] L) → J →ₐ[k] L),
        hopfPointPrecompose j b = (IsScalarTower.toAlgHom k E L).comp q ∧
        IsHopfPointCocycle d ∧
        precomposeHopfPointCocycle π d = twistHopfPointCocycle (inflateHopfPointCocycle (E := E) c) b ∧
        (IsHopfPointCoboundary d → IsHopfPointCoboundary c) := by
  obtain ⟨L, hEL, b, hb⟩ := exists_liftHopfPoint_after_finiteGalois E j hj q
  let i := IntermediateField.inclusion hEL
  letI : Algebra E L := i.toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algHom i
  letI : IsScalarTower k E L := finiteGaloisInclusion_scalarTower (k := k) hEL
  let C := inflateHopfPointCocycle (L := L) c
  have hC : IsHopfPointCocycle C := hc.inflate
  have hLift : hopfPointPrecompose j b = (IsScalarTower.toAlgHom k E L).comp q := hb
  have hOne (σ : L ≃ₐ[F] L) : hopfPointPrecompose j (twistHopfPointCocycle C b σ) = hopfPointOne := by
    rw [precompose_twistHopfPointCocycle, hLift]
    change twistHopfPointCocycle (precomposeHopfPointCocycle j (inflateHopfPointCocycle c))
      ((IsScalarTower.toAlgHom k E L).comp q) σ = hopfPointOne
    rw [precompose_inflateHopfPointCocycle]
    apply twistHopfPointCocycle_eq_one_of_witness
    exact hopfPointCoboundaryWitness_inflate (precomposeHopfPointCocycle j c) q hq σ
  obtain ⟨d, hd, hD⟩ := exists_kernelHopfPointCocycle j π hπ hker _ (hC.twist b) hOne
  refine ⟨L, hEL, b, d, hLift, hd, hD, ?_⟩
  intro htriv
  apply (isHopfPointCoboundary_inflate_iff (L := L) hc).mp
  apply isHopfPointCoboundary_of_twist b
  rw [← hD]
  exact htriv.precompose π

/-- Triviality of the image cocycle and of all finite Galois cocycles of the
actual kernel implies triviality of the original cocycle. -/
theorem isHopfPointCoboundary_of_quotient_and_kernel
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (j : Q →ₐc[k] H)
    (hj : letI : Algebra Q H := (j : Q →ₐ[k] H).toRingHom.toAlgebra; Module.FaithfullyFlat Q H)
    (π : H →ₐc[k] J) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : H →ₐ[k] J).toRingHom =
      (RingHom.ker (Bialgebra.counitAlgHom k Q).toRingHom).map (j : Q →ₐ[k] H).toRingHom)
    (c : (E ≃ₐ[F] E) → H →ₐ[k] E) (hc : IsHopfPointCocycle c)
    (hQ : IsHopfPointCoboundary (precomposeHopfPointCocycle j c))
    (hJ : ∀ (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
      (d : (L ≃ₐ[F] L) → J →ₐ[k] L), IsHopfPointCocycle d → IsHopfPointCoboundary d) :
    IsHopfPointCoboundary c := by
  obtain ⟨q, hq⟩ := hQ
  obtain ⟨L, _, _, d, _, hd, _, hBack⟩ :=
    exists_kernelCocycle_of_quotientCoboundary E j hj π hπ hker c hc q hq
  exact hBack (hJ L d hd)

/-- Specialize the cocycle reduction to the canonical Hopf algebra of the
identity fiber of the group map. -/
theorem isHopfPointCoboundary_of_quotient_and_hopfKernel
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (j : Q →ₐc[k] H)
    (hj : letI : Algebra Q H := (j : Q →ₐ[k] H).toRingHom.toAlgebra; Module.FaithfullyFlat Q H)
    (c : (E ≃ₐ[F] E) → H →ₐ[k] E) (hc : IsHopfPointCocycle c)
    (hQ : IsHopfPointCoboundary (precomposeHopfPointCocycle j c))
    (hJ : letI := (hopfKernelIdeal_isHopf j).quotientHopf
      ∀ (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
        (d : (L ≃ₐ[F] L) → (H ⧸ hopfKernelIdeal j) →ₐ[k] L),
        IsHopfPointCocycle d → IsHopfPointCoboundary d) :
    IsHopfPointCoboundary c := by
  let I := hopfKernelIdeal j
  letI := (hopfKernelIdeal_isHopf j).quotientHopf
  let π := (hopfKernelIdeal_isHopf j).quotientBialgHom
  exact isHopfPointCoboundary_of_quotient_and_kernel E j hj π
    (Ideal.Quotient.mkₐ_surjective k I) Ideal.mk_ker c hc hQ hJ

end QuotientFibers

end WideE
