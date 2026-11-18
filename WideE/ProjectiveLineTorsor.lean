import WideE.LineOrbitAction
import WideE.AffineTorsorQuotient
import WideE.ProjectiveLineStabilizer

/-! The line reduction of a torsor and its canonical chart under the stabilizer. -/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

open StrictEUnit

set_option maxHeartbeats 1000000

section LinePoints

variable {k R S H A ι : Type*} [Field k] [CommRing R] [CommRing S] [CommRing H] [CommRing A]
  [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S] [HopfAlgebra k H]
  [Algebra k A] [Algebra R A] [IsScalarTower k R A] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem map_scaled_vector {B C : Type*} [CommRing B] [CommRing C] [Algebra k B]
    [Algebra k C] (f : B →ₐ[k] C) (v : ι → k) (x : ι → B) (c : B)
    (h : x = c • (algebraMap k B ∘ v)) :
    f.toRingHom ∘ x = f c • (algebraMap k C ∘ v) := by
  funext i
  change f (x i) = f c * algebraMap k C (v i)
  rw [show x i = c * algebraMap k B (v i) from congrFun h i, map_mul, f.commutes]

omit [DecidableEq ι] [Fintype ι] [HopfAlgebra k H] in
private theorem exists_projectiveLinePoint_scalar (v : ι → k) (pivot : ι) (w : ι → S)
    (hPrimitive : Ideal.span (Set.range w) = ⊤) (p : ProjectiveLineReduction v pivot w →ₐ[R] A) :
    ∃ c : Aˣ, (p.comp (projectiveLineQuotient v pivot w)).toRingHom ∘ w =
      (c : A) • (algebraMap k A ∘ v) := by
  obtain ⟨c, hc⟩ := projectiveLineQuotient_unit_vector (R := R) v pivot w hPrimitive
  exact ⟨c.map p.toRingHom.toMonoidHom, map_scaled_vector (p.restrictScalars k) v _ _ hc⟩

variable (T : AffineHopfTorsor k R S H) (U : (Matrix ι ι H)ˣ)
  (g : (Matrix ι ι S)ˣ) (y : ι → R)
  (hg : g.val.map T.coaction.toRingHom = (U⁻¹).val.map
      (Algebra.TensorProduct.includeRight : H →ₐ[k] S ⊗[k] H).toRingHom *
    g.val.map (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] H).toRingHom)
  (v : ι → k) (pivot : ι) (hpivot : v pivot ≠ 0)
  (hPrimitive : Ideal.span (Set.range (projectiveFrameVector g y)) = ⊤)

local notation "w" => (projectiveFrameVector g y)
local notation "Q" => (ProjectiveLineReduction v pivot w)
local notation "π" => (projectiveLineQuotient (R := R) v pivot w)
local notation "J" => (projectiveLineStabilizerIdeal U v pivot)
local notation "K" => (H ⧸ (J))
local notation "ξ" => (Ideal.Quotient.mkₐ k (J))

include hg hpivot hPrimitive

/-- The group action of the line stabilizer carries points in the line
reduction to points in the same reduction. -/
theorem AffineHopfTorsor.exists_projectiveLineActPoint
    (p : Q →ₐ[R] A) (h : K →ₐ[k] A) :
    ∃ q : Q →ₐ[R] A, q.comp π = T.actPoint (p.comp π) (h.comp ξ) := by
  obtain ⟨c, hc⟩ := exists_projectiveLinePoint_scalar v pivot w hPrimitive p
  obtain ⟨d, hd⟩ := projectiveLineStabilizer_scale U v pivot hpivot
  have hd' : (ξ).toRingHom ∘ orbitVector U.val v =
      (d : K) • (algebraMap k K ∘ v) := (orbitVector_map ξ _ _).trans hd
  have hM := map_scaled_vector h v _ (d : K) hd'
  change (h.comp ξ).toRingHom ∘ orbitVector U.val v =
    h (d : K) • (algebraMap k A ∘ v) at hM
  rw [orbitVector_map] at hM
  let e := d.map h.toRingHom.toMonoidHom
  let M : (Matrix ι ι A)ˣ := U.map (h.comp ξ).toRingHom.mapMatrix.toMonoidHom
  have hMU : M.val *ᵥ (algebraMap k A ∘ v) = (e : A) • (algebraMap k A ∘ v) := hM
  have hAct := T.actPoint_projectiveFrameVector U g y hg (p.comp π) (h.comp ξ)
  change (T.actPoint (p.comp π) (h.comp ξ)).toRingHom ∘ w =
    M.inv *ᵥ ((p.comp π).toRingHom ∘ w) at hAct
  have hInv : M.inv *ᵥ (algebraMap k A ∘ v) = ((e⁻¹ : Aˣ) : A) • (algebraMap k A ∘ v) := by
    have h := congrArg (M.inv *ᵥ ·) hMU
    change M.inv *ᵥ (M.val *ᵥ (algebraMap k A ∘ v)) =
      M.inv *ᵥ ((e : A) • (algebraMap k A ∘ v)) at h
    rw [Matrix.mulVec_mulVec, M.inv_val, Matrix.one_mulVec, Matrix.mulVec_smul] at h
    calc
      _ = ((e⁻¹ : Aˣ) : A) • ((e : A) • (M.inv *ᵥ (algebraMap k A ∘ v))) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = _ := congrArg (((e⁻¹ : Aˣ) : A) • ·) h.symm
  rw [hc, Matrix.mulVec_smul, hInv, smul_smul] at hAct
  obtain ⟨q, hq, _⟩ := existsUnique_projectiveLinePoint v pivot hpivot w
    (T.actPoint (p.comp π) (h.comp ξ)) ((c : A) * ((e⁻¹ : Aˣ) : A)) hAct
  exact ⟨q, hq⟩

/-- The difference of two points of the reduction is a unique point of the
line stabilizer. The property is valid over all coefficient algebras. -/
theorem AffineHopfTorsor.existsUnique_projectiveLineGroupPoint (p q : Q →ₐ[R] A) :
    ∃! h : K →ₐ[k] A, T.actPoint (p.comp π) (h.comp ξ) = q.comp π := by
  obtain ⟨c, hc⟩ := exists_projectiveLinePoint_scalar v pivot w hPrimitive p
  obtain ⟨e, he⟩ := exists_projectiveLinePoint_scalar v pivot w hPrimitive q
  let a := T.pointDifference (p.comp π) (q.comp π)
  have ha := T.projectiveFrameVector_eq_mulVec_actPoint U g y hg (p.comp π) a
  change (p.comp π).toRingHom ∘ w =
    U.val.map a.toRingHom *ᵥ ((T.actPoint (p.comp π) a).toRingHom ∘ w) at ha
  rw [show T.actPoint (p.comp π) a = q.comp π from T.actPoint_pointDifference _ _,
    hc, he, Matrix.mulVec_smul] at ha
  have hScale : U.val.map a.toRingHom *ᵥ (algebraMap k A ∘ v) =
      (((e⁻¹ : Aˣ) : A) * (c : A)) • (algebraMap k A ∘ v) := by
    calc
      _ = ((e⁻¹ : Aˣ) : A) • ((e : A) • (U.val.map a.toRingHom *ᵥ (algebraMap k A ∘ v))) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = _ := by rw [← ha, smul_smul]
  have hScaled := (orbitVector_map a U.val v).trans hScale
  obtain ⟨h, hh, _⟩ := existsUnique_projectiveLinePoint (R := k) v pivot hpivot
    (orbitVector U.val v) a (((e⁻¹ : Aˣ) : A) * (c : A)) hScaled
  have hAct : T.actPoint (p.comp π) (h.comp ξ) = q.comp π := by
    rw [show h.comp ξ = a from hh]
    exact T.actPoint_pointDifference _ _
  refine ⟨h, hAct, fun j hj => ?_⟩
  apply Ideal.Quotient.algHom_ext
  exact T.actPoint_injective (p.comp π) (hj.trans hAct.symm)

end LinePoints

section LineTorsor

variable {k R S H ι : Type*} [Field k] [CommRing R] [CommRing S] [CommRing H]
  [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

variable (T : AffineHopfTorsor k R S H) (U : (Matrix ι ι H)ˣ)
  (g : (Matrix ι ι S)ˣ) (y : ι → R)
  (hg : g.val.map T.coaction.toRingHom = (U⁻¹).val.map
      (Algebra.TensorProduct.includeRight : H →ₐ[k] S ⊗[k] H).toRingHom *
    g.val.map (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] H).toRingHom)
  (v : ι → k) (pivot : ι) (hpivot : v pivot ≠ 0)
  (hPrimitive : Ideal.span (Set.range (projectiveFrameVector g y)) = ⊤)

local notation "w" => (projectiveFrameVector g y)
local notation "Q" => (ProjectiveLineReduction v pivot w)
local notation "π" => (projectiveLineQuotient (R := R) v pivot w)
local notation "J" => (projectiveLineStabilizerIdeal U v pivot)
local notation "K" => (H ⧸ (J))
local notation "ξ" => (Ideal.Quotient.mkₐ k (J))

include hg hpivot hPrimitive in
private theorem exists_projectiveLineCoaction :
    ∃ ρ : Q →ₐ[R] Q ⊗[k] K,
      ρ.comp π = (Algebra.TensorProduct.map π ξ).comp T.coaction := by
  let p := IsScalarTower.toAlgHom R Q (Q ⊗[k] K)
  let h : K →ₐ[k] Q ⊗[k] K := Algebra.TensorProduct.includeRight
  obtain ⟨ρ, hρ⟩ := T.exists_projectiveLineActPoint U g y hg v pivot hpivot hPrimitive p h
  have he : tensorPoint (p.comp π) (h.comp ξ) = Algebra.TensorProduct.map π ξ := by
    apply Algebra.TensorProduct.ext'
    intro s x
    rw [tensorPoint_tmul, Algebra.TensorProduct.map_tmul]
    change (π s ⊗ₜ[k] (1 : K)) * ((1 : Q) ⊗ₜ[k] ξ x) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨ρ, hρ.trans ?_⟩
  rw [AffineHopfTorsor.actPoint, he]

private theorem projectiveLineCoaction_actPoint {A : Type*}
    [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
    (ρ : Q →ₐ[R] Q ⊗[k] K) (hρ : ρ.comp π = (Algebra.TensorProduct.map π ξ).comp T.coaction)
    (p : Q →ₐ[R] A) (h : K →ₐ[k] A) :
    ((tensorPoint p h).comp ρ).comp π = T.actPoint (p.comp π) (h.comp ξ) := by
  have hMap : (tensorPoint p h).comp (Algebra.TensorProduct.map π ξ) =
      tensorPoint (p.comp π) (h.comp ξ) := by
    apply Algebra.TensorProduct.ext'
    intro s x
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, tensorPoint_tmul]
  rw [AlgHom.comp_assoc, hρ, ← AlgHom.comp_assoc, hMap, AffineHopfTorsor.actPoint]

include hg hpivot hPrimitive in
/-- The faithfully flat line reduction carries the descended coaction and
the canonical bijective chart for the actual Hopf quotient. -/
theorem AffineHopfTorsor.exists_projectiveLineTorsor
    (hJ : IsHopfIdeal k (J))
    (hFlat : Module.FaithfullyFlat R Q) :
    letI := hJ.quotientHopf
    ∃ TQ : AffineHopfTorsor k R Q K,
      TQ.coaction.comp π = (Algebra.TensorProduct.map π ξ).comp T.coaction := by
  letI := hJ.quotientHopf
  obtain ⟨ρ, hρ⟩ := exists_projectiveLineCoaction T U g y hg v pivot hpivot hPrimitive
  have hSurj : Function.Surjective (π) := Ideal.Quotient.mkₐ_surjective R (projectiveLineIdeal v pivot w)
  have hρ' : ρ.comp π = (Algebra.TensorProduct.map π (hJ.quotientBialgHom : H →ₐ[k] K)).comp
      T.coaction := hρ
  obtain ⟨hCoassoc, hCounit⟩ := quotient_coactionIdentities T π hSurj hJ.quotientBialgHom ρ hρ'
  have hCanonical : Function.Bijective (relativeCandidateCanonical ρ) := by
    apply canonical_bijective_of_pointDifference
    · let p := IsScalarTower.toAlgHom R Q (Q ⊗[R] Q)
      let q : Q →ₐ[R] Q ⊗[R] Q := Algebra.TensorProduct.includeRight
      obtain ⟨d, hd, _⟩ := T.existsUnique_projectiveLineGroupPoint U g y hg v pivot hpivot
        hPrimitive p q
      refine ⟨d, ?_⟩
      apply Ideal.Quotient.algHom_ext
      rw [projectiveLineCoaction_actPoint T U g y v pivot ρ hρ p d]
      exact hd
    · let p := IsScalarTower.toAlgHom R Q (Q ⊗[k] K)
      intro d e hde
      apply Ideal.Quotient.algHom_ext
      apply T.actPoint_injective (p.comp π)
      rw [← projectiveLineCoaction_actPoint T U g y v pivot ρ hρ p d,
        ← projectiveLineCoaction_actPoint T U g y v pivot ρ hρ p e,
        show (tensorPoint p d).comp ρ = (tensorPoint p e).comp ρ from hde]
  letI := T.group_finiteType
  exact ⟨⟨ρ, hCoassoc, hCounit, hCanonical, hFlat, Algebra.FiniteType.quotient k (J)⟩, hρ⟩

end LineTorsor

end WideE
