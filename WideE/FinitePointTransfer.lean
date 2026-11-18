import WideE.PolynomialRelationDescent

/-! Extending coefficients preserves a pointwise lifting assertion on a principal open. -/

noncomputable section

namespace WideE

section Lifting

variable {k Ω R S : Type*} [Field k] [IsAlgClosed k] [Field Ω] [IsAlgClosed Ω]
  [Algebra k Ω] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
  [Algebra.FiniteType k R] [Algebra.FiniteType k S]

/-- If all ground-field points on a principal open lift along a finite-type affine
morphism, the same holds over any algebraically closed coefficient field. -/
theorem exists_lift_of_principal_open_k_points (f : R →ₐ[k] S) (d₀ : R)
    (hLift : ∀ e : R →ₐ[k] k, e d₀ ≠ 0 → ∃ q : S →ₐ[k] k, q.comp f = e)
    (p : R →ₐ[k] Ω) (hp : p d₀ ≠ 0) : ∃ q : S →ₐ[k] Ω, q.comp f = p := by
  let I := RingHom.ker p.toRingHom
  let R' := R ⧸ I
  let J := Ideal.map f.toRingHom I
  let S' := S ⧸ J
  let π : R →ₐ[k] R' := Ideal.Quotient.mkₐ k I
  let ρ : S →ₐ[k] S' := Ideal.Quotient.mkₐ k J
  letI : I.IsPrime := RingHom.ker_isPrime p.toRingHom
  letI : IsDomain R' := inferInstance
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective k I
  letI : Algebra.FiniteType k R' := Algebra.FiniteType.of_surjective inferInstance π hπ
  letI : Algebra.FiniteType k S' := Algebra.FiniteType.of_surjective inferInstance ρ
    (Ideal.Quotient.mkₐ_surjective k J)
  let p' := Ideal.Quotient.liftₐ I p (fun _ h => h)
  have hp' : Function.Injective p' := by
    apply (injective_iff_map_eq_zero p').mpr
    intro x hx
    obtain ⟨a, rfl⟩ := hπ x
    change p a = 0 at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hJ : I ≤ RingHom.ker (ρ.comp f).toRingHom := by
    intro a ha
    change ρ (f a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f.toRingHom ha)
  let f' := Ideal.Quotient.liftₐ I (ρ.comp f) hJ
  let d' : R' := π d₀
  have hd' : d' ≠ 0 := by
    intro hd
    apply hp
    change p' d' = 0
    rw [hd, map_zero]
  have hLift' (e : R' →ₐ[k] k) (he : e d' ≠ 0) : ∃ q : S' →ₐ[k] k, q.comp f' = e := by
    obtain ⟨g, hg⟩ := hLift (e.comp π) he
    have hgJ : J ≤ RingHom.ker g.toRingHom := Ideal.map_le_iff_le_comap.mpr fun a ha => by
      change g (f a) = 0
      have hg' := DFunLike.congr_fun hg a
      change g (f a) = e (π a) at hg'
      rw [hg', show π a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    refine ⟨Ideal.Quotient.liftₐ J g hgJ, AlgHom.ext fun a' => ?_⟩
    obtain ⟨a, rfl⟩ := hπ a'
    exact DFunLike.congr_fun hg a
  have hInj := injective_of_principal_open_lifts f' d' hd' hLift'
  obtain ⟨d, hd, hLifts⟩ := exists_principal_open_lift_to_algClosed f' hInj
  obtain ⟨q', hq'⟩ := hLifts Ω p' (fun h => hd (hp' (h.trans (map_zero p').symm)))
  refine ⟨q'.comp ρ, AlgHom.ext fun a => ?_⟩
  exact DFunLike.congr_fun hq' (π a)

end Lifting

section Polynomials

variable {k Ω ι κ : Type*} [Field k] [IsAlgClosed k] [Field Ω] [IsAlgClosed Ω]
  [Algebra k Ω] [Finite ι] [Finite κ]

/-- Polynomial relations that have witnesses at every ground-field point of a
principal open also have witnesses at every extension-field point of that open. -/
theorem exists_polynomial_solution_to_algClosed
    (S : Set (MvPolynomial (ι ⊕ κ) k)) (d₀ : MvPolynomial ι k)
    (hLift : ∀ x : ι → k, MvPolynomial.aeval x d₀ ≠ 0 →
      ∃ y : κ → k, ∀ p ∈ S, MvPolynomial.aeval (Sum.elim x y) p = 0)
    (x : ι → Ω) (hx : MvPolynomial.aeval x d₀ ≠ 0) :
    ∃ y : κ → Ω, ∀ p ∈ S, MvPolynomial.aeval (Sum.elim x y) p = 0 := by
  let Q := PolynomialRelationAlgebra S
  let π : MvPolynomial (ι ⊕ κ) k →ₐ[k] Q := Ideal.Quotient.mkₐ k (Ideal.span S)
  let f : MvPolynomial ι k →ₐ[k] Q := π.comp (MvPolynomial.rename Sum.inl)
  letI : Algebra.FiniteType k (MvPolynomial (ι ⊕ κ) k) := Algebra.FiniteType.mvPolynomial k _
  have hF (p : MvPolynomial ι k →ₐ[k] k) (hp : p d₀ ≠ 0) : ∃ q : Q →ₐ[k] k, q.comp f = p := by
    let a (i : ι) := p (MvPolynomial.X i)
    have ha : MvPolynomial.aeval a = p := MvPolynomial.algHom_ext fun i => MvPolynomial.aeval_X a i
    obtain ⟨b, hb⟩ := hLift a (by rwa [ha])
    let q := (polynomialRelationPointEquiv S).symm ⟨Sum.elim a b, hb⟩
    refine ⟨q, MvPolynomial.algHom_ext fun i => ?_⟩
    change q (π (MvPolynomial.rename Sum.inl (MvPolynomial.X i))) = _
    rw [MvPolynomial.rename_X, polynomialRelationPointEquiv_symm_mk, MvPolynomial.aeval_X]
    rfl
  obtain ⟨q, hq⟩ := exists_lift_of_principal_open_k_points f d₀ hF (MvPolynomial.aeval x) hx
  let z := polynomialRelationPointEquiv S q
  let y (j : κ) := z.val (Sum.inr j)
  have hz : z.val = Sum.elim x y := by
    funext i
    cases i with
    | inl i =>
      change q (π (MvPolynomial.X (Sum.inl i))) = x i
      have h := DFunLike.congr_fun hq (MvPolynomial.X i)
      change q (π (MvPolynomial.rename Sum.inl (MvPolynomial.X i))) =
        MvPolynomial.aeval x (MvPolynomial.X i) at h
      rwa [MvPolynomial.rename_X, MvPolynomial.aeval_X] at h
    | inr j => rfl
  exact ⟨y, hz ▸ z.prop⟩

end Polynomials

end WideE
