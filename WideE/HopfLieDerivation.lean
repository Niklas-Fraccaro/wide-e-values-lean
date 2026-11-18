import WideE.AdjointRegularLocus

/-! The cotangent dual is the space of derivations at the Hopf counit. -/

open scoped TensorProduct

noncomputable section

namespace WideE

section Derivations

variable (F H A : Type*) [Field F] [CommRing H] [Bialgebra F H] [CommRing A] [Algebra F A]

local notation "ε" => Bialgebra.counitAlgHom F H
local notation "I" => hopfAugmentationIdeal F H

/-- Derivations from a Hopf algebra to the module defined by its counit. -/
def hopfCounitDerivations : Submodule F (H →ₗ[F] A) where
  carrier := {d | ∀ a b, d (a * b) = ε a • d b + ε b • d a}
  zero_mem' := by intro a b; simp
  add_mem' {d e} hd he := by
    intro a b
    change d (a * b) + e (a * b) = ε a • (d b + e b) + ε b • (d a + e a)
    rw [hd a b, he a b, smul_add, smul_add]
    abel
  smul_mem' t d hd := by
    intro a b
    change t • d (a * b) = ε a • (t • d b) + ε b • (t • d a)
    rw [hd a b, smul_add, smul_comm t (ε a), smul_comm t (ε b)]

theorem hopfCounitDerivations_mul (d : hopfCounitDerivations F H A) (a b : H) :
    d.val (a * b) = ε a • d.val b + ε b • d.val a :=
  d.prop a b

theorem hopfCounitDerivations_one (d : hopfCounitDerivations F H A) : d.val 1 = 0 := by
  have h := hopfCounitDerivations_mul F H A d 1 1
  have hε : (Bialgebra.counitAlgHom F H) 1 = 1 := map_one _
  rw [mul_one, hε, one_smul] at h
  calc
    d.val 1 = (d.val 1 + d.val 1) - d.val 1 := by abel
    _ = 0 := by rw [← h, sub_self]

theorem hopfCounitDerivations_algebraMap (d : hopfCounitDerivations F H A) (c : F) :
    d.val (algebraMap F H c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hopfCounitDerivations_one, smul_zero]

private def lieVectorToCounitDerivation : HopfLieVector F H A →ₗ[F] hopfCounitDerivations F H A where
  toFun := fun y => ⟨y.comp (hopfCotangentProjection F H), fun a b => by
    simp only [LinearMap.comp_apply, hopfCotangentProjection_mul, map_add, map_smul]⟩
  map_add' := fun _ _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' := fun _ _ => Subtype.ext (LinearMap.ext fun _ => rfl)

private def counitDerivationToLieVector (d : hopfCounitDerivations F H A) :
    HopfLieVector F H A := by
  let W := I • (⊤ : Submodule H I)
  refine (W.restrictScalars F).liftQ (d.val.comp ((I).restrictScalars F).subtype) ?_
  intro z hz
  change z ∈ W at hz
  change d.val z = 0
  refine Submodule.smul_induction_on (p := fun w : I => d.val w = 0) hz ?_ ?_
  · intro a ha b _
    have ha' : ε a = 0 := ha
    have hb' : ε (b : H) = 0 := b.prop
    change d.val (a * b) = 0
    rw [hopfCounitDerivations_mul, ha', hb', zero_smul, zero_smul, add_zero]
  · intro a b ha hb
    change d.val ((a : H) + (b : H)) = 0
    rw [map_add, ha, hb, add_zero]

private theorem counitDerivationToLieVector_projection (d : hopfCounitDerivations F H A) (a : H) :
    counitDerivationToLieVector F H A d (hopfCotangentProjection F H a) = d.val a := by
  change d.val (a - algebraMap F H (ε a)) = d.val a
  rw [map_sub, hopfCounitDerivations_algebraMap, sub_zero]

/-- The cotangent dual is linearly equivalent to the actual counit derivations. -/
def hopfLieDerivationEquiv : HopfLieVector F H A ≃ₗ[F] hopfCounitDerivations F H A :=
  LinearEquiv.ofBijective (lieVectorToCounitDerivation F H A)
    ⟨fun y z h => LinearMap.ext fun t => by
      obtain ⟨a, rfl⟩ := hopfCotangentProjection_surjective F H t
      exact LinearMap.congr_fun (congrArg Subtype.val h) a,
     fun d => ⟨counitDerivationToLieVector F H A d,
      Subtype.ext (LinearMap.ext (counitDerivationToLieVector_projection F H A d))⟩⟩

@[simp]
theorem hopfLieDerivationEquiv_apply (y : HopfLieVector F H A) (a : H) :
    (hopfLieDerivationEquiv F H A y).val a = y (hopfCotangentProjection F H a) := rfl

@[simp]
theorem hopfLieDerivationEquiv_symm_apply (d : hopfCounitDerivations F H A) (a : H) :
    (hopfLieDerivationEquiv F H A).symm d (hopfCotangentProjection F H a) = d.val a :=
  LinearMap.congr_fun (congrArg Subtype.val ((hopfLieDerivationEquiv F H A).apply_symm_apply d)) a

end Derivations

section InfinitesimalEquivalence

variable (F H A : Type*) [Field F] [CommRing H] [HopfAlgebra F H] [CommRing A] [Algebra F A]

/-- A dual-number point reducing to the identity point. -/
abbrev HopfInfinitesimalPoint :=
  {p : H →ₐ[F] DualNumber A //
    ∀ a : H, (p a).fst = algebraMap F A (Bialgebra.counitAlgHom F H a)}

private def infinitesimalCounitDerivation (p : HopfInfinitesimalPoint F H A) :
    hopfCounitDerivations F H A := ⟨
  ((TrivSqZeroExt.sndHom A A).restrictScalars F).comp p.val.toLinearMap,
  fun a b => by
    change (p.val (a * b)).snd = Bialgebra.counitAlgHom F H a • (p.val b).snd +
      Bialgebra.counitAlgHom F H b • (p.val a).snd
    rw [map_mul, DualNumber.snd_mul, p.prop a, p.prop b, Algebra.smul_def, Algebra.smul_def,
      mul_comm (p.val a).snd]⟩

/-- Every dual-number point reducing to the identity is uniquely the
point attached to a cotangent linear form. -/
def hopfInfinitesimalPointEquiv : HopfLieVector F H A ≃ HopfInfinitesimalPoint F H A where
  toFun y := ⟨hopfLieInfinitesimalPoint y, hopfLieInfinitesimalPoint_fst y⟩
  invFun p := (hopfLieDerivationEquiv F H A).symm (infinitesimalCounitDerivation F H A p)
  left_inv y := by
    apply (hopfLieDerivationEquiv F H A).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    rfl
  right_inv p := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · rw [hopfLieInfinitesimalPoint_fst, p.prop]
    · rw [hopfLieInfinitesimalPoint_snd, hopfLieDerivationEquiv_symm_apply]
      rfl

@[simp]
theorem hopfInfinitesimalPointEquiv_val (y : HopfLieVector F H A) :
    (hopfInfinitesimalPointEquiv F H A y).val = hopfLieInfinitesimalPoint y := rfl

end InfinitesimalEquivalence

end WideE
