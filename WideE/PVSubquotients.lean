import WideE.PVNaturality

/-! A horizontal split inclusion or projection transports a formal fundamental
matrix and its inverse to the algebra containing the larger system's matrix. -/

noncomputable section

namespace WideE

private def matrixUnitOfImages {S L ι : Type*} [CommRing S] [CommRing L]
    [Fintype ι] [DecidableEq ι] (e : S →+* L) (he : Function.Injective e)
    (Y : (Matrix ι ι L)ˣ) (u v : Matrix ι ι S)
    (hu : u.map e = Y.val) (hv : v.map e = (Y⁻¹).val) :
    {U : (Matrix ι ι S)ˣ // Units.map e.mapMatrix.toMonoidHom U = Y} := by
  have hmap : Function.Injective (e.mapMatrix : Matrix ι ι S →+* Matrix ι ι L) :=
    Matrix.map_injective he
  have huv : u * v = 1 := hmap (by
    rw [map_mul, map_one]
    change u.map e * v.map e = 1
    rw [hu, hv, Units.mul_inv])
  have hvu : v * u = 1 := hmap (by
    rw [map_mul, map_one]
    change v.map e * u.map e = 1
    rw [hv, hu, Units.inv_mul])
  exact ⟨⟨u, v, huv, hvu⟩, Units.ext hu⟩

private theorem inverse_intertwining {L ι κ : Type*} [CommRing L]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : (Matrix ι ι L)ˣ) (B : (Matrix κ κ L)ˣ) {F F₀ : Matrix κ ι L}
    (h : F * A.val = B.val * F₀) : F₀ * (A⁻¹).val = (B⁻¹).val * F := by
  calc
    F₀ * (A⁻¹).val = (B⁻¹).val * (B.val * F₀) * (A⁻¹).val := by
      rw [← Matrix.mul_assoc (B⁻¹).val, Units.inv_mul, Matrix.one_mul]
    _ = (B⁻¹).val * F := by
      simp only [← h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

section LaurentSystems

variable {K S : Type*} [Field K] [CommRing S]
variable [Algebra (LaurentPolynomial K) S]

local notation "R" => LaurentPolynomial K
local notation "P" => PowerSeries K
local notation "base" => algebraMap (LaurentPolynomial K) S

local instance subquotientPowerSeriesAlgebra : Algebra (LaurentPolynomial K) (PowerSeries K) :=
  (formalAtOne K).toRingHom.toAlgebra

private theorem map_baseMatrix {ι κ : Type*} (e : S →ₐ[R] P) (F : Matrix ι κ R) :
    (F.map base).map e.toRingHom = F.map (formalAtOne K).toRingHom := by
  apply Matrix.ext
  intro i j
  exact e.commutes (F i j)

private theorem map_fiberMatrix {ι κ : Type*} (F : Matrix ι κ R) :
    (F.map (LaurentPolynomial.C.comp (evalAtOne K))).map (formalAtOne K).toRingHom =
      F.map ((PowerSeries.C K).comp (evalAtOne K)) := by
  apply Matrix.ext
  intro i j
  exact formalAtOne_C K (evalAtOne K (F i j))

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- If the larger matrix lifts, the matrix and inverse for a split horizontal
subobject lift via the retraction over the Laurent ring and its fiber at one. -/
def liftFormalMatrixUnitOfSplitMono (e : S →ₐ[R] P) (he : Function.Injective e)
    (Y : (Matrix ι ι P)ˣ) (Z : (Matrix κ κ P)ˣ) (U : (Matrix κ κ S)ˣ)
    (hU : Units.map e.toRingHom.mapMatrix.toMonoidHom U = Z)
    (i : Matrix κ ι R) (r : Matrix ι κ R) (hr : r * i = 1)
    (hi : i.map (formalAtOne K) * Y.val =
      Z.val * (i.map (evalAtOne K)).map (PowerSeries.C K)) :
    {V : (Matrix ι ι S)ˣ // Units.map e.toRingHom.mapMatrix.toMonoidHom V = Y} := by
  let E := (formalAtOne K).toRingHom
  let F := LaurentPolynomial.C.comp (evalAtOne K)
  let E₀ := (PowerSeries.C K).comp (evalAtOne K)
  have hUval : U.val.map e.toRingHom = Z.val := congrArg Units.val hU
  let φ : (Matrix κ κ S)ˣ →* (Matrix κ κ P)ˣ :=
    Units.map e.toRingHom.mapMatrix.toMonoidHom
  have hUinv : (U⁻¹).val.map e.toRingHom = (Z⁻¹).val := by
    have h : φ U⁻¹ = Z⁻¹ := by rw [map_inv, show φ U = Z from hU]
    exact congrArg Units.val h
  have hrE : r.map E * i.map E = 1 := by
    rw [← Matrix.map_mul (f := E), hr, Matrix.map_one E E.map_zero E.map_one]
  have hrE₀ : r.map E₀ * i.map E₀ = 1 := by
    rw [← Matrix.map_mul (f := E₀), hr, Matrix.map_one E₀ E₀.map_zero E₀.map_one]
  change i.map E * Y.val = Z.val * i.map E₀ at hi
  have hInv := inverse_intertwining Y Z hi
  refine matrixUnitOfImages e.toRingHom he Y
    ((r.map base) * U.val * ((i.map F).map base))
    (((r.map F).map base) * (U⁻¹).val * (i.map base)) ?_ ?_
  · change ((r.map base) * U.val * ((i.map F).map base)).map e.toRingHom = Y.val
    simp only [Matrix.map_mul, map_baseMatrix, F, map_fiberMatrix, hUval]
    change r.map E * Z.val * i.map E₀ = Y.val
    rw [Matrix.mul_assoc, ← hi, ← Matrix.mul_assoc, hrE, Matrix.one_mul]
  · change (((r.map F).map base) * (U⁻¹).val * (i.map base)).map e.toRingHom = (Y⁻¹).val
    simp only [Matrix.map_mul, map_baseMatrix, F, map_fiberMatrix, hUinv]
    change r.map E₀ * (Z⁻¹).val * i.map E = (Y⁻¹).val
    rw [Matrix.mul_assoc, ← hInv, ← Matrix.mul_assoc, hrE₀, Matrix.one_mul]

/-- If the larger matrix lifts, the matrix and inverse for a split horizontal
quotient lift via the section over the Laurent ring and its fiber at one. -/
def liftFormalMatrixUnitOfSplitEpi (e : S →ₐ[R] P) (he : Function.Injective e)
    (Y : (Matrix ι ι P)ˣ) (Z : (Matrix κ κ P)ˣ) (U : (Matrix κ κ S)ˣ)
    (hU : Units.map e.toRingHom.mapMatrix.toMonoidHom U = Z)
    (p : Matrix ι κ R) (s : Matrix κ ι R) (hs : p * s = 1)
    (hp : p.map (formalAtOne K) * Z.val =
      Y.val * (p.map (evalAtOne K)).map (PowerSeries.C K)) :
    {V : (Matrix ι ι S)ˣ // Units.map e.toRingHom.mapMatrix.toMonoidHom V = Y} := by
  let E := (formalAtOne K).toRingHom
  let F := LaurentPolynomial.C.comp (evalAtOne K)
  let E₀ := (PowerSeries.C K).comp (evalAtOne K)
  have hUval : U.val.map e.toRingHom = Z.val := congrArg Units.val hU
  let φ : (Matrix κ κ S)ˣ →* (Matrix κ κ P)ˣ :=
    Units.map e.toRingHom.mapMatrix.toMonoidHom
  have hUinv : (U⁻¹).val.map e.toRingHom = (Z⁻¹).val := by
    have h : φ U⁻¹ = Z⁻¹ := by rw [map_inv, show φ U = Z from hU]
    exact congrArg Units.val h
  have hsE : p.map E * s.map E = 1 := by
    rw [← Matrix.map_mul (f := E), hs, Matrix.map_one E E.map_zero E.map_one]
  have hsE₀ : p.map E₀ * s.map E₀ = 1 := by
    rw [← Matrix.map_mul (f := E₀), hs, Matrix.map_one E₀ E₀.map_zero E₀.map_one]
  change p.map E * Z.val = Y.val * p.map E₀ at hp
  have hInv := inverse_intertwining Z Y hp
  refine matrixUnitOfImages e.toRingHom he Y
    ((p.map base) * U.val * ((s.map F).map base))
    (((p.map F).map base) * (U⁻¹).val * (s.map base)) ?_ ?_
  · change ((p.map base) * U.val * ((s.map F).map base)).map e.toRingHom = Y.val
    simp only [Matrix.map_mul, map_baseMatrix, F, map_fiberMatrix, hUval]
    change p.map E * Z.val * s.map E₀ = Y.val
    rw [hp, Matrix.mul_assoc, hsE₀, Matrix.mul_one]
  · change (((p.map F).map base) * (U⁻¹).val * (s.map base)).map e.toRingHom = (Y⁻¹).val
    simp only [Matrix.map_mul, map_baseMatrix, F, map_fiberMatrix, hUinv]
    change p.map E₀ * (Z⁻¹).val * s.map E = (Y⁻¹).val
    rw [hInv, Matrix.mul_assoc, hsE, Matrix.mul_one]

variable [CharZero K] {m n : ℕ}
variable {A : Matrix (Fin m) (Fin m) (LaurentPolynomial K)}
variable {B : Matrix (Fin n) (Fin n) (LaurentPolynomial K)}

/-- The normalized formal solution of a split horizontal subobject lifts to the
same coefficient algebra as the normalized solution of the larger system. -/
def liftFundamentalMatrixOfHorizontalSubobject
    (e : S →ₐ[R] P) (he : Function.Injective e) (U : (Matrix (Fin n) (Fin n) S)ˣ)
    (hU : Units.map e.toRingHom.mapMatrix.toMonoidHom U = formalFundamentalAtOneUnit B)
    (i : Matrix (Fin n) (Fin m) R) (r : Matrix (Fin m) (Fin n) R) (hr : r * i = 1)
    (hi : i.map laurentDerivation = B * i - i * A) :
    {V : (Matrix (Fin m) (Fin m) S)ˣ //
      Units.map e.toRingHom.mapMatrix.toMonoidHom V = formalFundamentalAtOneUnit A} := by
  exact liftFormalMatrixUnitOfSplitMono e he (formalFundamentalAtOneUnit A) (formalFundamentalAtOneUnit B)
    U hU i r hr (formalFundamentalAtOneUnit_naturality (A := A) (B := B) i hi)

/-- The normalized formal solution of a split horizontal quotient lifts to the
same coefficient algebra as the normalized solution of the larger system. -/
def liftFundamentalMatrixOfHorizontalQuotient
    (e : S →ₐ[R] P) (he : Function.Injective e) (U : (Matrix (Fin n) (Fin n) S)ˣ)
    (hU : Units.map e.toRingHom.mapMatrix.toMonoidHom U = formalFundamentalAtOneUnit B)
    (p : Matrix (Fin m) (Fin n) R) (s : Matrix (Fin n) (Fin m) R) (hs : p * s = 1)
    (hp : p.map laurentDerivation = A * p - p * B) :
    {V : (Matrix (Fin m) (Fin m) S)ˣ //
      Units.map e.toRingHom.mapMatrix.toMonoidHom V = formalFundamentalAtOneUnit A} := by
  exact liftFormalMatrixUnitOfSplitEpi e he (formalFundamentalAtOneUnit A) (formalFundamentalAtOneUnit B)
    U hU p s hs (formalFundamentalAtOneUnit_naturality (A := B) (B := A) p hp)

end LaurentSystems

/-- The underlying short exact sequence with a free last term gives the two
matrix splittings used for descent of the two end terms. Their specializations
are the corresponding splittings of the fiber at one. -/
theorem exists_splitMatrices_of_shortExact {R M N Q ι κ τ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]
    (bM : Basis ι R M) (bN : Basis κ R N) (bQ : Basis τ R Q)
    (i : M →ₗ[R] N) (p : N →ₗ[R] Q) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hExact : Function.Exact i p) :
    (∃ r : Matrix ι κ R, r * LinearMap.toMatrix bM bN i = 1) ∧
    (∃ s : Matrix κ τ R, LinearMap.toMatrix bN bQ p * s = 1) := by
  letI : Module.Free R Q := Module.Free.of_basis bQ
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  have hsplit : (∃ l : Q →ₗ[R] N, p.comp l = LinearMap.id) ↔
      ∃ l : N →ₗ[R] M, l.comp i = LinearMap.id :=
    (hExact.split_tfae hi hp).out 0 1
  obtain ⟨r, hr⟩ := hsplit.mp ⟨s, hs⟩
  refine ⟨⟨LinearMap.toMatrix bN bM r, ?_⟩, ⟨LinearMap.toMatrix bQ bN s, ?_⟩⟩
  · rw [← LinearMap.toMatrix_comp bM bN bM, hr, LinearMap.toMatrix_id]
  · rw [← LinearMap.toMatrix_comp bQ bN bQ, hs, LinearMap.toMatrix_id]

end WideE
