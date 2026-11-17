import WideE.CentralDivisionC1

/-!
# Central simple algebras over characteristic-zero C₁ fields

The endomorphism ring of a simple module is a division ring. Density with
coefficients in that division ring shows that its center is the base field.
The division-algebra result then makes every commuting endomorphism scalar.
-/

noncomputable section

namespace WideE

/-- A finite-dimensional central simple algebra over a characteristic-zero C₁
field is a full matrix algebra over that field. -/
theorem centralSimple_splits_of_isC1 (K S : Type*)
    [Field K] [CharZero K] [Ring S] [Algebra K S]
    [Algebra.IsCentral K S] [IsSimpleRing S] [FiniteDimensional K S] (hK : IsC1 K) :
    ∃ m : ℕ, 0 < m ∧ Nonempty (S ≃ₐ[K] Matrix (Fin m) (Fin m) K) := by
  classical
  obtain ⟨I, hI, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal S) bot_ne_top
  let M := S ⧸ I
  letI : IsSimpleModule S M := isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hI)
  letI : Nontrivial M := IsSimpleModule.nontrivial S M
  letI : FiniteDimensional K M := Module.Finite.of_surjective
    ((Submodule.mkQ I).restrictScalars K) (Submodule.mkQ_surjective I)
  let E := Module.End S M
  letI : DecidableEq E := Classical.decEq _
  letI : DivisionRing E := Module.End.instDivisionRing
  letI : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite K E M
  let F : E →ₗ[K] Module.End K M :=
    { toFun := fun f => f.restrictScalars K
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  letI : FiniteDimensional K E := Module.Finite.of_injective F fun _ _ h =>
    LinearMap.ext fun v => LinearMap.congr_fun h v
  let ρ : S →ₐ[K] Module.End K M := Algebra.lsmul K K M
  have hρ : Function.Injective ρ := ρ.toRingHom.injective
  have hDense : Function.Surjective (DistribMulAction.toLinearMap E M : S → Module.End E M) :=
    simple_module_action_surjective (K := E) fun f => ⟨f, fun _ => rfl⟩
  letI : Algebra.IsCentral K E := ⟨by
    intro f hf
    let f' : Module.End E M :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := by
          intro g v
          change f (g v) = g (f v)
          exact (congrArg (fun a : E => a v) (Subalgebra.mem_center_iff.mp hf g)).symm }
    obtain ⟨a, ha⟩ := hDense f'
    have hAction (v : M) : a • v = f v := LinearMap.congr_fun ha v
    have hCentral : a ∈ Subalgebra.center K S := by
      apply Subalgebra.mem_center_iff.mpr
      intro b
      apply hρ
      apply LinearMap.ext
      intro v
      change (b * a) • v = (a * b) • v
      simp only [mul_smul, hAction, map_smul]
    obtain ⟨c, hc⟩ := (inferInstance : Algebra.IsCentral K S).out hCentral
    change algebraMap K S c = a at hc
    refine ⟨c, LinearMap.ext fun v => ?_⟩
    change c • v = f v
    rw [← IsScalarTower.algebraMap_smul S c v, hc, hAction]⟩
  obtain ⟨e⟩ := centralDivision_algEquiv_base_of_isC1 K E hK
  have hScalars (f : Module.End S M) : ∃ c : K, ∀ v : M, f v = c • v := by
    refine ⟨e f, fun v => ?_⟩
    have hf := e.symm.commutes (e f)
    change e.symm (e f) = algebraMap K E (e f) at hf
    rw [AlgEquiv.symm_apply_apply] at hf
    exact congrArg (fun a : E => a v) hf
  have hSurj : Function.Surjective ρ :=
    simple_module_action_surjective (K := K) hScalars
  refine ⟨Module.finrank K M, Module.finrank_pos, ?_⟩
  exact ⟨(AlgEquiv.ofBijective ρ ⟨hρ, hSurj⟩).trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K M))⟩

end WideE
