import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Variables
noncomputable section
namespace MvPolynomial
open Finsupp
variable {σ : Type*} {τ : Type*}
variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
def bind₁ (f : σ → MvPolynomial τ R) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval f
def bind₂ (f : R →+* MvPolynomial σ S) : MvPolynomial σ R →+* MvPolynomial σ S :=
  eval₂Hom f X
def join₁ : MvPolynomial (MvPolynomial σ R) R →ₐ[R] MvPolynomial σ R :=
  aeval id
def join₂ : MvPolynomial σ (MvPolynomial σ R) →+* MvPolynomial σ R :=
  eval₂Hom (RingHom.id _) X
@[simp]
theorem aeval_eq_bind₁ (f : σ → MvPolynomial τ R) : aeval f = bind₁ f :=
  rfl
@[simp]
theorem eval₂Hom_C_eq_bind₁ (f : σ → MvPolynomial τ R) : eval₂Hom C f = bind₁ f :=
  rfl
@[simp]
theorem eval₂Hom_eq_bind₂ (f : R →+* MvPolynomial σ S) : eval₂Hom f X = bind₂ f :=
  rfl
section
variable (σ R)
@[simp]
theorem aeval_id_eq_join₁ : aeval id = @join₁ σ R _ :=
  rfl
theorem eval₂Hom_C_id_eq_join₁ (φ : MvPolynomial (MvPolynomial σ R) R) :
    eval₂Hom C id φ = join₁ φ :=
  rfl
@[simp]
theorem eval₂Hom_id_X_eq_join₂ : eval₂Hom (RingHom.id _) X = @join₂ σ R _ :=
  rfl
end
attribute [-simp]
  aeval_eq_bind₁ eval₂Hom_C_eq_bind₁ eval₂Hom_eq_bind₂ aeval_id_eq_join₁ eval₂Hom_id_X_eq_join₂
@[simp]
theorem bind₁_X_right (f : σ → MvPolynomial τ R) (i : σ) : bind₁ f (X i) = f i :=
  aeval_X f i
@[simp]
theorem bind₂_X_right (f : R →+* MvPolynomial σ S) (i : σ) : bind₂ f (X i) = X i :=
  eval₂Hom_X' f X i
@[simp]
theorem bind₁_X_left : bind₁ (X : σ → MvPolynomial σ R) = AlgHom.id R _ := by
  ext1 i
  simp
variable (f : σ → MvPolynomial τ R)
theorem bind₁_C_right (f : σ → MvPolynomial τ R) (x) : bind₁ f (C x) = C x := algHom_C _ _
@[simp]
theorem bind₂_C_right (f : R →+* MvPolynomial σ S) (r : R) : bind₂ f (C r) = f r :=
  eval₂Hom_C f X r
@[simp]
theorem bind₂_C_left : bind₂ (C : R →+* MvPolynomial σ R) = RingHom.id _ := by ext : 2 <;> simp
@[simp]
theorem bind₂_comp_C (f : R →+* MvPolynomial σ S) : (bind₂ f).comp C = f :=
  RingHom.ext <| bind₂_C_right _
@[simp]
theorem join₂_map (f : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    join₂ (map f φ) = bind₂ f φ := by simp only [join₂, bind₂, eval₂Hom_map_hom, RingHom.id_comp]
@[simp]
theorem join₂_comp_map (f : R →+* MvPolynomial σ S) : join₂.comp (map f) = bind₂ f :=
  RingHom.ext <| join₂_map _
theorem aeval_id_rename (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    aeval id (rename f p) = aeval f p := by rw [aeval_rename, Function.id_comp]
@[simp]
theorem join₁_rename (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    join₁ (rename f φ) = bind₁ f φ :=
  aeval_id_rename _ _
@[simp]
theorem bind₁_id : bind₁ (@id (MvPolynomial σ R)) = join₁ :=
  rfl
@[simp]
theorem bind₂_id : bind₂ (RingHom.id (MvPolynomial σ R)) = join₂ :=
  rfl
theorem bind₁_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R)
    (φ : MvPolynomial σ R) : (bind₁ g) (bind₁ f φ) = bind₁ (fun i => bind₁ g (f i)) φ := by
  simp [bind₁, ← comp_aeval]
theorem bind₁_comp_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R) :
    (bind₁ g).comp (bind₁ f) = bind₁ fun i => bind₁ g (f i) := by
  ext1
  apply bind₁_bind₁
theorem bind₂_comp_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T) :
    (bind₂ g).comp (bind₂ f) = bind₂ ((bind₂ g).comp f) := by ext : 2 <;> simp
theorem bind₂_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T)
    (φ : MvPolynomial σ R) : (bind₂ g) (bind₂ f φ) = bind₂ ((bind₂ g).comp f) φ :=
  RingHom.congr_fun (bind₂_comp_bind₂ f g) φ
theorem rename_comp_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) :
    (rename g).comp (bind₁ f) = bind₁ fun i => rename g <| f i := by
  ext1 i
  simp
theorem rename_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) (φ : MvPolynomial σ R) :
    rename g (bind₁ f φ) = bind₁ (fun i => rename g <| f i) φ :=
  AlgHom.congr_fun (rename_comp_bind₁ f g) φ
theorem map_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* T) (φ : MvPolynomial σ R) :
    map g (bind₂ f φ) = bind₂ ((map g).comp f) φ := by
  simp only [bind₂, eval₂_comp_right, coe_eval₂Hom, eval₂_map]
  congr 1 with : 1
  simp only [Function.comp_apply, map_X]
theorem bind₁_comp_rename {υ : Type*} (f : τ → MvPolynomial υ R) (g : σ → τ) :
    (bind₁ f).comp (rename g) = bind₁ (f ∘ g) := by
  ext1 i
  simp
theorem bind₁_rename {υ : Type*} (f : τ → MvPolynomial υ R) (g : σ → τ) (φ : MvPolynomial σ R) :
    bind₁ f (rename g φ) = bind₁ (f ∘ g) φ :=
  AlgHom.congr_fun (bind₁_comp_rename f g) φ
theorem bind₂_map (f : S →+* MvPolynomial σ T) (g : R →+* S) (φ : MvPolynomial σ R) :
    bind₂ f (map g φ) = bind₂ (f.comp g) φ := by simp [bind₂]
@[simp]
theorem map_comp_C (f : R →+* S) : (map f).comp (C : R →+* MvPolynomial σ R) = C.comp f := by
  ext1
  apply map_C
theorem hom_bind₁ (f : MvPolynomial τ R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    f (bind₁ g φ) = eval₂Hom (f.comp C) (fun i => f (g i)) φ := by
  rw [bind₁, map_aeval, algebraMap_eq]
theorem map_bind₁ (f : R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g i)) (map f φ) := by
  rw [hom_bind₁, map_comp_C, ← eval₂Hom_map_hom]
  rfl
@[simp]
theorem eval₂Hom_comp_C (f : R →+* S) (g : σ → S) : (eval₂Hom f g).comp C = f := by
  ext1 r
  exact eval₂_C f g r
theorem eval₂Hom_bind₁ (f : R →+* S) (g : τ → S) (h : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval₂Hom f g (bind₁ h φ) = eval₂Hom f (fun i => eval₂Hom f g (h i)) φ := by
  rw [hom_bind₁, eval₂Hom_comp_C]
theorem aeval_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    aeval f (bind₁ g φ) = aeval (fun i => aeval f (g i)) φ :=
  eval₂Hom_bind₁ _ _ _ _
theorem aeval_comp_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) :
    (aeval f).comp (bind₁ g) = aeval fun i => aeval f (g i) := by
  ext1
  apply aeval_bind₁
theorem eval₂Hom_comp_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S) :
    (eval₂Hom f g).comp (bind₂ h) = eval₂Hom ((eval₂Hom f g).comp h) g := by ext : 2 <;> simp
theorem eval₂Hom_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S)
    (φ : MvPolynomial σ R) : eval₂Hom f g (bind₂ h φ) = eval₂Hom ((eval₂Hom f g).comp h) g φ :=
  RingHom.congr_fun (eval₂Hom_comp_bind₂ f g h) φ
theorem aeval_bind₂ [Algebra S T] (f : σ → T) (g : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    aeval f (bind₂ g φ) = eval₂Hom ((↑(aeval f : _ →ₐ[S] _) : _ →+* _).comp g) f φ :=
  eval₂Hom_bind₂ _ _ _ _
alias eval₂Hom_C_left := eval₂Hom_C_eq_bind₁
theorem bind₁_monomial (f : σ → MvPolynomial τ R) (d : σ →₀ ℕ) (r : R) :
    bind₁ f (monomial d r) = C r * ∏ i ∈ d.support, f i ^ d i := by
  simp only [monomial_eq, map_mul, bind₁_C_right, Finsupp.prod, map_prod,
    map_pow, bind₁_X_right]
theorem bind₂_monomial (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) (r : R) :
    bind₂ f (monomial d r) = f r * monomial d 1 := by
  simp only [monomial_eq, RingHom.map_mul, bind₂_C_right, Finsupp.prod, map_prod,
    map_pow, bind₂_X_right, C_1, one_mul]
@[simp]
theorem bind₂_monomial_one (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) :
    bind₂ f (monomial d 1) = monomial d 1 := by rw [bind₂_monomial, f.map_one, one_mul]
section
theorem vars_bind₁ [DecidableEq τ] (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    (bind₁ f φ).vars ⊆ φ.vars.biUnion fun i => (f i).vars := by
  calc (bind₁ f φ).vars
    _ = (φ.support.sum fun x : σ →₀ ℕ => (bind₁ f) (monomial x (coeff x φ))).vars := by
      rw [← map_sum, ← φ.as_sum]
    _ ≤ φ.support.biUnion fun i : σ →₀ ℕ => ((bind₁ f) (monomial i (coeff i φ))).vars :=
      (vars_sum_subset _ _)
    _ = φ.support.biUnion fun d : σ →₀ ℕ => vars (C (coeff d φ) * ∏ i ∈ d.support, f i ^ d i) := by
      simp only [bind₁_monomial]
    _ ≤ φ.support.biUnion fun d : σ →₀ ℕ => d.support.biUnion fun i => vars (f i) := ?_
    _ ≤ φ.vars.biUnion fun i : σ => vars (f i) := ?_
  · apply Finset.biUnion_mono
    intro d _hd
    calc
      vars (C (coeff d φ) * ∏ i ∈ d.support, f i ^ d i) ≤
          (C (coeff d φ)).vars ∪ (∏ i ∈ d.support, f i ^ d i).vars :=
        vars_mul _ _
      _ ≤ (∏ i ∈ d.support, f i ^ d i).vars := by
        simp only [Finset.empty_union, vars_C, Finset.le_iff_subset, Finset.Subset.refl]
      _ ≤ d.support.biUnion fun i : σ => vars (f i ^ d i) := vars_prod _
      _ ≤ d.support.biUnion fun i : σ => (f i).vars := ?_
    apply Finset.biUnion_mono
    intro i _hi
    apply vars_pow
  · intro j
    simp_rw [Finset.mem_biUnion]
    rintro ⟨d, hd, ⟨i, hi, hj⟩⟩
    exact ⟨i, (mem_vars _).mpr ⟨d, hd, hi⟩, hj⟩
end
theorem mem_vars_bind₁ (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) {j : τ}
    (h : j ∈ (bind₁ f φ).vars) : ∃ i : σ, i ∈ φ.vars ∧ j ∈ (f i).vars := by
  classical
  simpa only [exists_prop, Finset.mem_biUnion, mem_support_iff, Ne] using vars_bind₁ f φ h
instance monad : Monad fun σ => MvPolynomial σ R where
  map f p := rename f p
  pure := X
  bind p f := bind₁ f p
instance lawfulFunctor : LawfulFunctor fun σ => MvPolynomial σ R where
  map_const := by intros; rfl
  id_map := by intros; simp [(· <$> ·)]
  comp_map := by intros; simp [(· <$> ·)]
instance lawfulMonad : LawfulMonad fun σ => MvPolynomial σ R where
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; simp [bind, ← bind₁_comp_bind₁]
  seqLeft_eq := by intros; simp [SeqLeft.seqLeft, Seq.seq, (· <$> ·), bind₁_rename]; rfl
  seqRight_eq := by intros; simp [SeqRight.seqRight, Seq.seq, (· <$> ·), bind₁_rename]; rfl
  pure_seq := by intros; simp [(· <$> ·), pure, Seq.seq]
  bind_pure_comp := by aesop
  bind_map := by aesop
end MvPolynomial