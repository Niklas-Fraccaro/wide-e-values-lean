import AlgebraicPoint
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! Idempotents in a tensor product over an algebraically closed field. -/

noncomputable section

open scoped TensorProduct

namespace WideE

open StrictEUnit

/-- Every idempotent of a preconnected affine spectrum is zero or one. -/
theorem idempotent_eq_zero_or_one_of_preconnected {R : Type*} [CommRing R]
    [PreconnectedSpace (PrimeSpectrum R)] {e : R} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hc with h | h
  · left
    have h' : PrimeSpectrum.basicOpen e = PrimeSpectrum.basicOpen (0 : R) := by
      rw [PrimeSpectrum.basicOpen_zero]
      exact TopologicalSpace.Opens.ext h
    have hE : E ⟨e, he⟩ = E ⟨0, IsIdempotentElem.zero⟩ := by
      apply TopologicalSpace.Clopens.ext
      change (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) =
        (PrimeSpectrum.basicOpen (0 : R) : Set (PrimeSpectrum R))
      rw [h']
    exact congrArg Subtype.val (E.injective hE)
  · right
    have h' : PrimeSpectrum.basicOpen e = PrimeSpectrum.basicOpen (1 : R) := by
      rw [PrimeSpectrum.basicOpen_one]
      exact TopologicalSpace.Opens.ext h
    have hE : E ⟨e, he⟩ = E ⟨1, IsIdempotentElem.one⟩ := by
      apply TopologicalSpace.Clopens.ext
      change (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) =
        (PrimeSpectrum.basicOpen (1 : R) : Set (PrimeSpectrum R))
      rw [h']
    exact congrArg Subtype.val (E.injective hE)

section Points

variable {k A B : Type*} [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]

/-- Vanishing at every rational point of a finite-type algebra over an
algebraically closed field detects the nilradical. -/
theorem isNilpotent_of_eq_zero_at_points {e : A}
    (hz : ∀ p : A →ₐ[k] k, p e = 0) : IsNilpotent e := by
  letI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have h : e ∈ (⊥ : Ideal A).radical := by
    rw [Ideal.radical_eq_jacobson, Ideal.jacobson, Ideal.mem_sInf]
    intro m hm
    letI : m.IsMaximal := hm.2
    rw [← maximalIdealPoint_ker (k := k) m]
    exact hz (maximalIdealPoint (k := k) m)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h
  exact ⟨n, Ideal.mem_bot.mp hn⟩

/-- An idempotent that vanishes at all rational points is zero. -/
theorem idempotent_eq_zero_of_points {e : A} (he : IsIdempotentElem e)
    (hz : ∀ p : A →ₐ[k] k, p e = 0) : e = 0 := by
  obtain ⟨n, hn0⟩ := isNilpotent_of_eq_zero_at_points hz
  have hn1 : e ^ (n + 1) = 0 := by rw [pow_succ, hn0, zero_mul]
  rwa [he.pow_succ_eq] at hn1

/-- Two idempotents agreeing at all rational points give the same clopen part. -/
theorem idempotent_eq_of_points {e f : A} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : ∀ p : A →ₐ[k] k, p e = p f) : e = f := by
  have hef : e * (1 - f) = 0 := idempotent_eq_zero_of_points (k := k) (he.mul hf.one_sub) (fun p => by
    rw [map_mul, map_sub, map_one, ← h p, mul_sub, mul_one, (he.map p).eq, sub_self])
  have hfe : f * (1 - e) = 0 := idempotent_eq_zero_of_points (k := k) (hf.mul he.one_sub) (fun p => by
    rw [map_mul, map_sub, map_one, h p, mul_sub, mul_one, (hf.map p).eq, sub_self])
  rw [mul_sub, mul_one, sub_eq_zero] at hef hfe
  exact hef.trans ((mul_comm e f).trans hfe.symm)

private def tensorEvalLeft (p : A →ₐ[k] k) : A ⊗[k] B →ₐ[k] B :=
  Algebra.TensorProduct.lift ((Algebra.ofId k B).comp p) (AlgHom.id k B)
    (fun _ _ => Commute.all _ _)

private def tensorEvalRight (q : B →ₐ[k] k) : A ⊗[k] B →ₐ[k] A :=
  Algebra.TensorProduct.lift (AlgHom.id k A) ((Algebra.ofId k A).comp q)
    (fun _ _ => Commute.all _ _)

omit [IsAlgClosed k] [Algebra.FiniteType k A] [Algebra.FiniteType k B] in
private theorem tensorEval_eq (p : A →ₐ[k] k) (q : B →ₐ[k] k) (e : A ⊗[k] B) :
    q (tensorEvalLeft p e) = p (tensorEvalRight q e) := by
  have h : q.comp (tensorEvalLeft p) = p.comp (tensorEvalRight q) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change q (algebraMap k B (p a) * b) = p (a * algebraMap k A (q b))
    rw [map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
    rfl
  exact congrFun (congrArg DFunLike.coe h) e

omit [IsAlgClosed k] [Algebra.FiniteType k A] [Algebra.FiniteType k B] in
private theorem tensorPoint_eval (p : A ⊗[k] B →ₐ[k] k) (e : A ⊗[k] B) :
    p e = (p.comp Algebra.TensorProduct.includeRight)
      (tensorEvalLeft (p.comp Algebra.TensorProduct.includeLeft) e) := by
  have h : p = (p.comp Algebra.TensorProduct.includeRight).comp
      (tensorEvalLeft (p.comp Algebra.TensorProduct.includeLeft)) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change p (a ⊗ₜ[k] b) = (p.comp Algebra.TensorProduct.includeRight)
      (algebraMap k B (p (a ⊗ₜ[k] (1 : B))) * b)
    rw [map_mul, AlgHom.commutes]
    change _ = p (a ⊗ₜ[k] (1 : B)) * p ((1 : A) ⊗ₜ[k] b)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact congrFun (congrArg DFunLike.coe h) e

/-- Tensoring the coordinate rings of two connected affine schemes of
finite type over an algebraically closed field creates no new components. -/
theorem idempotent_tensor_eq_zero_or_one [Nontrivial B]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    {e : A ⊗[k] B} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  classical
  letI : Algebra.FiniteType k (A ⊗[k] B) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  let q := Classical.choice (nonempty_algebraic_point (k := k) (S := B))
  obtain ⟨c, hc, hConst⟩ : ∃ c : k, (c = 0 ∨ c = 1) ∧
      tensorEvalRight q e = algebraMap k A c := by
    rcases hA _ (he.map (tensorEvalRight q)) with h0 | h1
    · exact ⟨0, Or.inl rfl, h0.trans (map_zero _).symm⟩
    · exact ⟨1, Or.inr rfl, h1.trans (map_one _).symm⟩
  have hPoint (p : A ⊗[k] B →ₐ[k] k) : p e = c := by
    let pA : A →ₐ[k] k := p.comp Algebra.TensorProduct.includeLeft
    let pB : B →ₐ[k] k := p.comp Algebra.TensorProduct.includeRight
    let x := tensorEvalLeft pA e
    have hq : q x = c := by
      change q (tensorEvalLeft pA e) = _
      rw [tensorEval_eq, hConst, AlgHom.commutes]
      rfl
    have hp : p e = pB x := tensorPoint_eval p e
    rcases hB x (he.map (tensorEvalLeft pA)) with hx | hx
    · rw [hp, hx, map_zero]
      simpa only [hx, map_zero] using hq
    · rw [hp, hx, map_one]
      simpa only [hx, map_one] using hq
  rcases hc with rfl | rfl
  · exact Or.inl (idempotent_eq_zero_of_points he hPoint)
  · right
    have hZero := idempotent_eq_zero_of_points (k := k) he.one_sub
      (fun p => by rw [map_sub, map_one, hPoint, sub_self])
    exact (sub_eq_zero.mp hZero).symm

end Points

end WideE
