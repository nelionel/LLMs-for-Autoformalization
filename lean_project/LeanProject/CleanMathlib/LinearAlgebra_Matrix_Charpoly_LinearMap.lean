import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLin
variable {ι : Type*} [Fintype ι]
variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)
variable (b : ι → M)
open Polynomial Matrix
def PiToModule.fromMatrix [DecidableEq ι] : Matrix ι ι R →ₗ[R] (ι → R) →ₗ[R] M :=
  (LinearMap.llcomp R _ _ _ (Fintype.linearCombination R R b)).comp algEquivMatrix'.symm.toLinearMap
theorem PiToModule.fromMatrix_apply [DecidableEq ι] (A : Matrix ι ι R) (w : ι → R) :
    PiToModule.fromMatrix R b A w = Fintype.linearCombination R R b (A *ᵥ w) :=
  rfl
theorem PiToModule.fromMatrix_apply_single_one [DecidableEq ι] (A : Matrix ι ι R) (j : ι) :
    PiToModule.fromMatrix R b A (Pi.single j 1) = ∑ i : ι, A i j • b i := by
  rw [PiToModule.fromMatrix_apply, Fintype.linearCombination_apply, Matrix.mulVec_single]
  simp_rw [mul_one]
def PiToModule.fromEnd : Module.End R M →ₗ[R] (ι → R) →ₗ[R] M :=
  LinearMap.lcomp _ _ (Fintype.linearCombination R R b)
theorem PiToModule.fromEnd_apply (f : Module.End R M) (w : ι → R) :
    PiToModule.fromEnd R b f w = f (Fintype.linearCombination R R b w) :=
  rfl
theorem PiToModule.fromEnd_apply_single_one [DecidableEq ι] (f : Module.End R M) (i : ι) :
    PiToModule.fromEnd R b f (Pi.single i 1) = f (b i) := by
  rw [PiToModule.fromEnd_apply]
  congr
  convert Fintype.linearCombination_apply_single (S := R) R b i (1 : R)
  rw [one_smul]
theorem PiToModule.fromEnd_injective (hb : Submodule.span R (Set.range b) = ⊤) :
    Function.Injective (PiToModule.fromEnd R b) := by
  intro x y e
  ext m
  obtain ⟨m, rfl⟩ : m ∈ LinearMap.range (Fintype.linearCombination R R b) := by
    rw [(Fintype.range_linearCombination R b).trans hb]
    exact Submodule.mem_top
  exact (LinearMap.congr_fun e m : _)
section
variable {R} [DecidableEq ι]
def Matrix.Represents (A : Matrix ι ι R) (f : Module.End R M) : Prop :=
  PiToModule.fromMatrix R b A = PiToModule.fromEnd R b f
variable {b}
theorem Matrix.Represents.congr_fun {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
    (x) : Fintype.linearCombination R R b (A *ᵥ x) = f (Fintype.linearCombination R R b x) :=
  LinearMap.congr_fun h x
theorem Matrix.represents_iff {A : Matrix ι ι R} {f : Module.End R M} :
    A.Represents b f ↔
      ∀ x, Fintype.linearCombination R R b (A *ᵥ x) = f (Fintype.linearCombination R R b x) :=
  ⟨fun e x => e.congr_fun x, fun H => LinearMap.ext fun x => H x⟩
theorem Matrix.represents_iff' {A : Matrix ι ι R} {f : Module.End R M} :
    A.Represents b f ↔ ∀ j, ∑ i : ι, A i j • b i = f (b j) := by
  constructor
  · intro h i
    have := LinearMap.congr_fun h (Pi.single i 1)
    rwa [PiToModule.fromEnd_apply_single_one, PiToModule.fromMatrix_apply_single_one] at this
  · intro h
    ext
    simp_rw [LinearMap.comp_apply, LinearMap.coe_single, PiToModule.fromEnd_apply_single_one,
      PiToModule.fromMatrix_apply_single_one]
    apply h
theorem Matrix.Represents.mul {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : Matrix.Represents b A' f') : (A * A').Represents b (f * f') := by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, _root_.map_mul]
  ext
  dsimp [PiToModule.fromEnd]
  rw [← h'.congr_fun, ← h.congr_fun]
  rfl
theorem Matrix.Represents.one : (1 : Matrix ι ι R).Represents b 1 := by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, _root_.map_one]
  ext
  rfl
theorem Matrix.Represents.add {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : Matrix.Represents b A' f') : (A + A').Represents b (f + f') := by
  delta Matrix.Represents at h h' ⊢; rw [map_add, map_add, h, h']
theorem Matrix.Represents.zero : (0 : Matrix ι ι R).Represents b 0 := by
  delta Matrix.Represents
  rw [map_zero, map_zero]
theorem Matrix.Represents.smul {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
    (r : R) : (r • A).Represents b (r • f) := by
  delta Matrix.Represents at h ⊢
  rw [_root_.map_smul, _root_.map_smul, h]
theorem Matrix.Represents.algebraMap (r : R) :
    (algebraMap _ (Matrix ι ι R) r).Represents b (algebraMap _ (Module.End R M) r) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using Matrix.Represents.one.smul r
theorem Matrix.Represents.eq (hb : Submodule.span R (Set.range b) = ⊤)
    {A : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : A.Represents b f') : f = f' :=
  PiToModule.fromEnd_injective R b hb (h.symm.trans h')
variable (b R)
def Matrix.isRepresentation : Subalgebra R (Matrix ι ι R) where
  carrier := { A | ∃ f : Module.End R M, A.Represents b f }
  mul_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ * f₂, e₁.mul e₂⟩
  one_mem' := ⟨1, Matrix.Represents.one⟩
  add_mem' := fun ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ + f₂, e₁.add e₂⟩
  zero_mem' := ⟨0, Matrix.Represents.zero⟩
  algebraMap_mem' r := ⟨algebraMap _ _ r, .algebraMap _⟩
variable (hb : Submodule.span R (Set.range b) = ⊤)
include hb
noncomputable def Matrix.isRepresentation.toEnd :
    Matrix.isRepresentation R b →ₐ[R] Module.End R M where
  toFun A := A.2.choose
  map_one' := (1 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.one
  map_mul' A₁ A₂ := (A₁ * A₂).2.choose_spec.eq hb (A₁.2.choose_spec.mul A₂.2.choose_spec)
  map_zero' := (0 : Matrix.isRepresentation R b).2.choose_spec.eq hb Matrix.Represents.zero
  map_add' A₁ A₂ := (A₁ + A₂).2.choose_spec.eq hb (A₁.2.choose_spec.add A₂.2.choose_spec)
  commutes' r :=
    (algebraMap _ (Matrix.isRepresentation R b) r).2.choose_spec.eq hb (.algebraMap r)
theorem Matrix.isRepresentation.toEnd_represents (A : Matrix.isRepresentation R b) :
    (A : Matrix ι ι R).Represents b (Matrix.isRepresentation.toEnd R b hb A) :=
  A.2.choose_spec
theorem Matrix.isRepresentation.eq_toEnd_of_represents (A : Matrix.isRepresentation R b)
    {f : Module.End R M} (h : (A : Matrix ι ι R).Represents b f) :
    Matrix.isRepresentation.toEnd R b hb A = f :=
  A.2.choose_spec.eq hb h
theorem Matrix.isRepresentation.toEnd_exists_mem_ideal (f : Module.End R M) (I : Ideal R)
    (hI : LinearMap.range f ≤ I • ⊤) :
    ∃ M, Matrix.isRepresentation.toEnd R b hb M = f ∧ ∀ i j, M.1 i j ∈ I := by
  have : ∀ x, f x ∈ LinearMap.range (Ideal.finsuppTotal ι M I b) := by
    rw [Ideal.range_finsuppTotal, hb]
    exact fun x => hI (LinearMap.mem_range_self f x)
  choose bM' hbM' using this
  let A : Matrix ι ι R := fun i j => bM' (b j) i
  have : A.Represents b f := by
    rw [Matrix.represents_iff']
    dsimp [A]
    intro j
    specialize hbM' (b j)
    rwa [Ideal.finsuppTotal_apply_eq_of_fintype] at hbM'
  exact
    ⟨⟨A, f, this⟩, Matrix.isRepresentation.eq_toEnd_of_represents R b hb ⟨A, f, this⟩ this,
      fun i j => (bM' (b j) i).prop⟩
theorem Matrix.isRepresentation.toEnd_surjective :
    Function.Surjective (Matrix.isRepresentation.toEnd R b hb) := by
  intro f
  obtain ⟨M, e, -⟩ := Matrix.isRepresentation.toEnd_exists_mem_ideal R b hb f ⊤ (by simp)
  exact ⟨M, e⟩
end
theorem LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul
    [Module.Finite R M] (f : Module.End R M) (I : Ideal R) (hI : LinearMap.range f ≤ I • ⊤) :
    ∃ p : R[X], p.Monic ∧ (∀ k, p.coeff k ∈ I ^ (p.natDegree - k)) ∧ Polynomial.aeval f p = 0 := by
  classical
    cases subsingleton_or_nontrivial R
    · exact ⟨0, Polynomial.monic_of_subsingleton _, by simp⟩
    obtain ⟨s : Finset M, hs : Submodule.span R (s : Set M) = ⊤⟩ :=
      Module.Finite.out (R := R) (M := M)
    obtain ⟨A, H, h⟩ :=
      Matrix.isRepresentation.toEnd_exists_mem_ideal R ((↑) : s → M)
        (by rw [Subtype.range_coe_subtype, Finset.setOf_mem, hs]) f I hI
    rw [← H]
    refine ⟨A.1.charpoly, A.1.charpoly_monic, ?_, ?_⟩
    · rw [A.1.charpoly_natDegree_eq_dim]
      exact coeff_charpoly_mem_ideal_pow h
    · rw [Polynomial.aeval_algHom_apply,
        ← map_zero (Matrix.isRepresentation.toEnd R ((↑) : s → M) _)]
      congr 1
      ext1
      rw [Polynomial.aeval_subalgebra_coe, Matrix.aeval_self_charpoly, Subalgebra.coe_zero]
theorem LinearMap.exists_monic_and_aeval_eq_zero [Module.Finite R M] (f : Module.End R M) :
    ∃ p : R[X], p.Monic ∧ Polynomial.aeval f p = 0 :=
  (LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul R f ⊤ (by simp)).imp
    fun _ h => h.imp_right And.right