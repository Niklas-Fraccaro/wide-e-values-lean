import WideE.AdjointDominance
import WideE.AdjointLieDifferential
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The adjoint family has full differential when the Cartan directions
span the zero weight space and the adjoint operator spans the other weights. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

section Eigenspaces

variable {k M ρ : Type*} [Field k] [AddCommGroup M] [Module k M]

/-- The nonzero eigendirections lie in the image. If the eigenspaces span,
adding a space containing the kernel recovers the whole module. -/
theorem range_sup_eq_top_of_eigenspaces (D : Module.End k M) (a : ρ → k)
    (hSpan : (⨆ j, Module.End.eigenspace D (a j)) = ⊤)
    (V : Submodule k M) (hV : LinearMap.ker D ≤ V) :
    LinearMap.range D ⊔ V = ⊤ := by
  apply top_unique
  rw [← hSpan]
  apply iSup_le
  intro j x hx
  have h := Module.End.mem_eigenspace_iff.mp hx
  by_cases hj : a j = 0
  · apply Submodule.mem_sup_right
    apply hV
    change D x = 0
    simpa only [hj, zero_smul] using h
  · apply Submodule.mem_sup_left
    refine ⟨(a j)⁻¹ • x, ?_⟩
    rw [map_smul, h, smul_smul, inv_mul_cancel₀ hj, one_smul]

end Eigenspaces

section Directions

variable {k H τ : Type*} [Field k] [CommRing H] [HopfAlgebra k H] [Fintype τ]

local notation "𝔤" => HopfLieVector k H k
local notation "L" => hopfInvariantDerivations k H
local notation "θ" => (hopfLieVectorInvariantDerivations (k := k) (H := H))

private theorem exists_adjointFamilyDirection (v : τ → 𝔤) (x₀ : 𝔤)
    (hSpan : LinearMap.range (LieModule.toEnd k L L (θ x₀)) ⊔
      Submodule.span k (Set.range fun j => θ (v j)) = ⊤) (x : 𝔤) :
    ∃ u : 𝔤, ∃ d : τ → k, (θ).symm ⁅θ u, θ x₀⁆ + ∑ j, d j • v j = x := by
  let D := LieModule.toEnd k L L (θ x₀)
  let V := Submodule.span k (Set.range fun j => θ (v j))
  have hTop : θ x ∈ LinearMap.range D ⊔ V := by rw [hSpan]; trivial
  obtain ⟨a, ha, z, hz, hSum⟩ := Submodule.mem_sup.mp hTop
  obtain ⟨u, rfl⟩ := ha
  change z ∈ Submodule.span k (Set.range fun j => θ (v j)) at hz
  rw [← Fintype.range_linearCombination] at hz
  obtain ⟨d, hd⟩ := hz
  refine ⟨-(θ).symm u, d, (θ).injective ?_⟩
  rw [map_add, LinearEquiv.apply_symm_apply, map_neg, LinearEquiv.apply_symm_apply, neg_lie, lie_skew,
    map_sum]
  simp_rw [map_smul]
  have hd' : (∑ j, d j • θ (v j)) = z := hd
  rw [hd']
  exact hSum

private def adjointFamilyLinearForm (v : τ → 𝔤) (ℓ : 𝔤 →ₗ[k] k) : MvPolynomial τ k :=
  ∑ j, MvPolynomial.C (ℓ (v j)) * MvPolynomial.X j

private theorem adjointFamilyLinearForm_aeval {E : Type*} [CommRing E] [Algebra k E]
    (v : τ → 𝔤) (ℓ : 𝔤 →ₗ[k] k) (a : τ → E) :
    MvPolynomial.aeval a (adjointFamilyLinearForm v ℓ) =
      ∑ j, a j * algebraMap k E (ℓ (v j)) := by
  simp only [adjointFamilyLinearForm, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, mul_comm]

end Directions

section AdjointOpen

variable {k H ι η τ ρ : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [IsDomain H] [Algebra.FiniteType k H]
  [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η] [Fintype τ] [Fintype ρ]

local notation "𝔤" => HopfLieVector k H k
local notation "L" => hopfInvariantDerivations k H
local notation "θ" => (hopfLieVectorInvariantDerivations (k := k) (H := H))

universe uΩ

set_option maxHeartbeats 1200000 in
/-- A spanning adjoint differential yields a uniform open of conjugates with
the prescribed nonzero polynomial condition on their parameters. -/
theorem exists_hopfAdjointFamily_principal_open_avoiding_of_adjoint_span
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (b : Basis η k (HopfCotangent k H)) (v : τ → 𝔤) (a : τ → k)
    (hSpan : LinearMap.range (LieModule.toEnd k L L (θ (∑ j, a j • v j))) ⊔
      Submodule.span k (Set.range fun j => θ (v j)) = ⊤)
    (d₀ : MvPolynomial τ k) (hd₀ : d₀ ≠ 0) :
    ∃ f : MvPolynomial η k, f ≠ 0 ∧ ∀ (Ω : Type uΩ) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
      (x : HopfLieVector k H Ω), MvPolynomial.aeval (fun i => x (b i)) f ≠ 0 →
      ∃ (g : H →ₐ[k] Ω) (c : τ → Ω), MvPolynomial.aeval c d₀ ≠ 0 ∧
        x = hopfAdjoint g (∑ j, c j • (Algebra.ofId k Ω).toLinearMap.comp (v j)) := by
  classical
  let x₀ := ∑ j, a j • v j
  choose u d h using fun r : η => exists_adjointFamilyDirection v x₀ hSpan (b.coord r)
  have hJ : (Matrix.of fun r i =>
      (hopfAdjointTangentMatrix b (fun j => (∑ s, a s • v s) (b j)) *ᵥ fun j => u r (b j)) i +
        ∑ s, d r s * v s (b i)).det ≠ 0 := by
    have hI : Matrix.of (fun r i =>
        (hopfAdjointTangentMatrix b (fun j => x₀ (b j)) *ᵥ fun j => u r (b j)) i +
          ∑ s, d r s * v s (b i)) = 1 := by
      apply Matrix.ext
      intro r i
      change (hopfAdjointTangentMatrix b (fun j => x₀ (b j)) *ᵥ fun j => u r (b j)) i +
          ∑ s, d r s * v s (b i) = _
      rw [hopfAdjointTangentMatrix_mulVec_eq_lieBracket U hΔ hε hGen b x₀ (u r)]
      have he := congrArg (fun x : 𝔤 => x (b i)) (h r)
      simpa only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, Matrix.one_apply, eq_comm] using he
    change (Matrix.of fun r i =>
      (hopfAdjointTangentMatrix b (fun j => x₀ (b j)) *ᵥ fun j => u r (b j)) i +
        ∑ s, d r s * v s (b i)).det ≠ 0
    rw [hI, Matrix.det_one]
    exact one_ne_zero
  exact exists_hopfAdjointFamily_principal_open_avoiding_to_algClosed_of_jacobian
    b v a u d d₀ hd₀ hJ

set_option maxHeartbeats 1200000 in
/-- Spanning by the adjoint image and the parameter space at a Cartan
direction gives a ground-field open of geometric conjugates. Linear forms
nonzero at that direction remain simultaneously nonzero in the chosen parameters. -/
theorem exists_hopfAdjointFamily_principal_open_of_adjoint_span
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (b : Basis η k (HopfCotangent k H)) (v : τ → 𝔤) (a : τ → k)
    (hSpan : LinearMap.range (LieModule.toEnd k L L (θ (∑ j, a j • v j))) ⊔
      Submodule.span k (Set.range fun j => θ (v j)) = ⊤)
    (ℓ : ρ → 𝔤 →ₗ[k] k) (hAvoid : ∀ i, ℓ i (∑ j, a j • v j) ≠ 0) :
    ∃ f : MvPolynomial η k, f ≠ 0 ∧ ∀ (Ω : Type uΩ) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
      (x : HopfLieVector k H Ω), MvPolynomial.aeval (fun i => x (b i)) f ≠ 0 →
      ∃ (g : H →ₐ[k] Ω) (c : τ → Ω),
        x = hopfAdjoint g (∑ j, c j • (Algebra.ofId k Ω).toLinearMap.comp (v j)) ∧
        ∀ i, ∑ j, c j * algebraMap k Ω (ℓ i (v j)) ≠ 0 := by
  let s₀ : MvPolynomial τ k := ∏ i, adjointFamilyLinearForm v (ℓ i)
  have hs : s₀ ≠ 0 := by
    have hEval : MvPolynomial.aeval a s₀ ≠ 0 := by
      change MvPolynomial.aeval a (∏ i, adjointFamilyLinearForm v (ℓ i)) ≠ 0
      rw [map_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      rw [adjointFamilyLinearForm_aeval]
      simpa only [map_sum, map_smul, smul_eq_mul, Algebra.id.map_eq_id, RingHom.id_apply] using hAvoid i
    exact fun h => hEval (h ▸ map_zero _)
  obtain ⟨f, hf, hm⟩ := exists_hopfAdjointFamily_principal_open_avoiding_of_adjoint_span
    U hΔ hε hGen b v a hSpan s₀ hs
  refine ⟨f, hf, ?_⟩
  intro Ω _ _ _ x hx
  obtain ⟨g, c, hNonzero, hConj⟩ := hm Ω x hx
  refine ⟨g, c, hConj, fun i => ?_⟩
  change MvPolynomial.aeval c (∏ i, adjointFamilyLinearForm v (ℓ i)) ≠ 0 at hNonzero
  rw [map_prod] at hNonzero
  simpa only [adjointFamilyLinearForm_aeval] using
    Finset.prod_ne_zero_iff.mp hNonzero i (Finset.mem_univ i)

end AdjointOpen

end WideE
