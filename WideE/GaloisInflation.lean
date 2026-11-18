import WideE.GaloisTorsor

/-!
# Inflation of Galois cocycles of Hopf-algebra points

A Galois cocycle becomes a coboundary over a larger Galois extension exactly
when it already has a coboundary over its original field of definition.
-/

noncomputable section

open scoped TensorProduct

namespace WideE

section HopfPoints

variable {k H A B : Type*} [CommRing k] [CommRing H] [CommRing A] [CommRing B]
variable [Bialgebra k H] [Algebra k A] [Algebra k B]

@[simp] theorem hopfPointMul_one_left (g : H →ₐ[k] A) :
    hopfPointMul hopfPointOne g = g := by
  have hEval (z : H ⊗[k] H) :
      Algebra.TensorProduct.lift (hopfPointOne : H →ₐ[k] A) g (fun _ _ => Commute.all _ _) z =
        Algebra.TensorProduct.lift (Algebra.ofId k A) g (fun _ _ => Commute.all _ _)
          ((Coalgebra.counit (R := k) (A := H)).rTensor H z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply AlgHom.ext
  intro h
  change Algebra.TensorProduct.lift (hopfPointOne : H →ₐ[k] A) g (fun _ _ => Commute.all _ _)
    (Coalgebra.comul (R := k) h) = g h
  rw [hEval, Coalgebra.rTensor_counit_comul]
  simp

theorem hopfPointMul_postcompose (f : A →ₐ[k] B) (g h : H →ₐ[k] A) :
    f.comp (hopfPointMul g h) = hopfPointMul (f.comp g) (f.comp h) := by
  have hEval (z : H ⊗[k] H) :
      f (Algebra.TensorProduct.lift g h (fun _ _ => Commute.all _ _) z) =
        Algebra.TensorProduct.lift (f.comp g) (f.comp h) (fun _ _ => Commute.all _ _) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp only [Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.comp_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  apply AlgHom.ext
  intro a
  exact hEval (Coalgebra.comul (R := k) a)

@[simp] theorem hopfPointOne_postcompose (f : A →ₐ[k] B) :
    f.comp (hopfPointOne : H →ₐ[k] A) = hopfPointOne :=
  AlgHom.ext fun h => f.commutes (Bialgebra.counitAlgHom k H h)

end HopfPoints

section Inflation

variable {k F E L H : Type*} [CommRing k] [Field F] [Field E] [Field L] [CommRing H]
variable [Algebra k F] [Algebra k E] [Algebra k L] [HopfAlgebra k H]
variable [Algebra F E] [Algebra F L] [Algebra E L]
variable [IsScalarTower F E L] [IsScalarTower k F E] [IsScalarTower k F L]
variable [IsScalarTower k E L] [Normal F E]

/-- Inflate a cocycle by restricting automorphisms and extending its point values. -/
def inflateHopfPointCocycle (c : (E ≃ₐ[F] E) → H →ₐ[k] E) (σ : L ≃ₐ[F] L) :
    H →ₐ[k] L :=
  (IsScalarTower.toAlgHom k E L).comp (c (AlgEquiv.restrictNormalHom E σ))

private theorem comp_algebraMap_restrictNormalHom (σ : L ≃ₐ[F] L) (g : H →ₐ[k] E) :
    (σ.toAlgHom.restrictScalars k).comp ((IsScalarTower.toAlgHom k E L).comp g) =
      (IsScalarTower.toAlgHom k E L).comp
        (((AlgEquiv.restrictNormalHom E σ).toAlgHom.restrictScalars k).comp g) :=
  AlgHom.ext fun h => (σ.restrictNormal_commutes E (g h)).symm

theorem IsHopfPointCocycle.inflate {c : (E ≃ₐ[F] E) → H →ₐ[k] E}
    (hc : IsHopfPointCocycle c) :
    IsHopfPointCocycle (inflateHopfPointCocycle (L := L) c) := by
  constructor
  · simp only [inflateHopfPointCocycle, map_one, hc.1, hopfPointOne_postcompose]
  · intro σ τ
    simp only [inflateHopfPointCocycle, map_mul, hc.2, hopfPointMul_postcompose,
      comp_algebraMap_restrictNormalHom]

theorem IsHopfPointCoboundary.inflate {c : (E ≃ₐ[F] E) → H →ₐ[k] E}
    (hc : IsHopfPointCoboundary c) :
    IsHopfPointCoboundary (inflateHopfPointCocycle (L := L) c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨(IsScalarTower.toAlgHom k E L).comp b, fun σ => ?_⟩
  rw [inflateHopfPointCocycle, comp_algebraMap_restrictNormalHom,
    ← hopfPointMul_postcompose, hb]

/-- Triviality after inflation descends along a larger Galois extension. -/
theorem isHopfPointCoboundary_inflate_iff [IsGalois F L]
    {c : (E ≃ₐ[F] E) → H →ₐ[k] E} (hc : IsHopfPointCocycle c) :
    IsHopfPointCoboundary (inflateHopfPointCocycle (L := L) c) ↔ IsHopfPointCoboundary c := by
  refine ⟨?_, fun h => h.inflate⟩
  rintro ⟨b, hb⟩
  letI := IsGalois.tower_top_of_isGalois F E L
  let incl := IsScalarTower.toAlgHom k E L
  have hFixed (σ : L ≃ₐ[E] L) (a : H) : σ (b a) = b a := by
    have hRestr : AlgEquiv.restrictNormalHom E (σ.restrictScalars F) = 1 := by
      apply AlgEquiv.ext
      intro x
      apply (algebraMap E L).injective
      exact ((σ.restrictScalars F).restrictNormal_commutes E x).trans (σ.commutes x)
    have h := hb (σ.restrictScalars F)
    rw [inflateHopfPointCocycle, hRestr, hc.1, hopfPointOne_postcompose,
      hopfPointMul_one_left] at h
    exact DFunLike.congr_fun h a
  have hMem (a : H) : b a ∈ incl.range := by
    have h : b a ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[E] L)) :=
      (IntermediateField.mem_fixedField_iff _ _).mpr (fun σ _ => hFixed σ a)
    rw [InfiniteGalois.fixedField_bot] at h
    exact IntermediateField.mem_bot.mp h
  let e := AlgEquiv.ofInjective incl (algebraMap E L).injective
  let b₀ := e.symm.toAlgHom.comp (b.codRestrict incl.range hMem)
  have hb₀ : incl.comp b₀ = b :=
    AlgHom.ext fun a => congrArg Subtype.val (e.apply_symm_apply (b.codRestrict incl.range hMem a))
  refine ⟨b₀, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) L τ
  have h := hb σ
  rw [inflateHopfPointCocycle, hσ, ← hb₀, comp_algebraMap_restrictNormalHom, hσ,
    ← hopfPointMul_postcompose] at h
  exact AlgHom.ext fun a => (algebraMap E L).injective (DFunLike.congr_fun h a)

end Inflation

end WideE
