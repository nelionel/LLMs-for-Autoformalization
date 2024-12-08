import Mathlib.Algebra.MvPolynomial.CommRing
noncomputable section
open Function Set Subalgebra MvPolynomial Algebra
open scoped Classical
variable {ι ι' : Type*} (R : Type*) {K A A' : Type*} (x : ι → A)
variable [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
def AlgebraicIndependent : Prop :=
  Injective (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A)
variable {R} {x}
theorem algebraicIndependent_iff :
    AlgebraicIndependent R x ↔
      ∀ p : MvPolynomial ι R, MvPolynomial.aeval (x : ι → A) p = 0 → p = 0 :=
  injective_iff_map_eq_zero _
theorem AlgebraicIndependent.eq_zero_of_aeval_eq_zero (h : AlgebraicIndependent R x) :
    ∀ p : MvPolynomial ι R, MvPolynomial.aeval (x : ι → A) p = 0 → p = 0 :=
  algebraicIndependent_iff.1 h
theorem algebraicIndependent_iff_injective_aeval :
    AlgebraicIndependent R x ↔ Injective (MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A) :=
  Iff.rfl
namespace AlgebraicIndependent
theorem of_comp (f : A →ₐ[R] A') (hfv : AlgebraicIndependent R (f ∘ x)) :
    AlgebraicIndependent R x := by
  have : aeval (f ∘ x) = f.comp (aeval x) := by ext; simp
  rw [AlgebraicIndependent, this, AlgHom.coe_comp] at hfv
  exact hfv.of_comp
variable (hx : AlgebraicIndependent R x)
include hx
theorem comp (f : ι' → ι) (hf : Function.Injective f) : AlgebraicIndependent R (x ∘ f) := by
  intro p q
  simpa [aeval_rename, (rename_injective f hf).eq_iff] using @hx (rename f p) (rename f q)
theorem coe_range : AlgebraicIndependent R ((↑) : range x → A) := by
  simpa using hx.comp _ (rangeSplitting_injective x)
end AlgebraicIndependent
open AlgebraicIndependent
theorem algebraicIndependent_equiv (e : ι ≃ ι') {f : ι' → A} :
    AlgebraicIndependent R (f ∘ e) ↔ AlgebraicIndependent R f :=
  ⟨fun h => Function.comp_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
    fun h => h.comp _ e.injective⟩
theorem algebraicIndependent_equiv' (e : ι ≃ ι') {f : ι' → A} {g : ι → A} (h : f ∘ e = g) :
    AlgebraicIndependent R g ↔ AlgebraicIndependent R f :=
  h ▸ algebraicIndependent_equiv e
theorem algebraicIndependent_subtype_range {ι} {f : ι → A} (hf : Injective f) :
    AlgebraicIndependent R ((↑) : range f → A) ↔ AlgebraicIndependent R f :=
  Iff.symm <| algebraicIndependent_equiv' (Equiv.ofInjective f hf) rfl
alias ⟨AlgebraicIndependent.of_subtype_range, _⟩ := algebraicIndependent_subtype_range
theorem algebraicIndependent_image {ι} {s : Set ι} {f : ι → A} (hf : Set.InjOn f s) :
    (AlgebraicIndependent R fun x : s => f x) ↔ AlgebraicIndependent R fun x : f '' s => (x : A) :=
  algebraicIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl
namespace AlgebraicIndependent
theorem mono {t s : Set A} (h : t ⊆ s)
    (hx : AlgebraicIndependent R ((↑) : s → A)) : AlgebraicIndependent R ((↑) : t → A) := by
  simpa [Function.comp] using hx.comp (inclusion h) (inclusion_injective h)
section repr
variable (hx : AlgebraicIndependent R x)
include hx
@[simps! apply_coe]
def aevalEquiv : MvPolynomial ι R ≃ₐ[R] Algebra.adjoin R (range x) :=
  (AlgEquiv.ofInjective (aeval x) (algebraicIndependent_iff_injective_aeval.1 hx)).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_range_eq_range_aeval R x).symm)
theorem algebraMap_aevalEquiv (p : MvPolynomial ι R) :
    algebraMap (Algebra.adjoin R (range x)) A (hx.aevalEquiv p) = aeval x p :=
  rfl
def repr : Algebra.adjoin R (range x) →ₐ[R] MvPolynomial ι R :=
  hx.aevalEquiv.symm
@[simp]
theorem aeval_repr (p) : aeval x (hx.repr p) = p :=
  Subtype.ext_iff.1 (AlgEquiv.apply_symm_apply hx.aevalEquiv p)
theorem aeval_comp_repr : (aeval x).comp hx.repr = Subalgebra.val _ :=
  AlgHom.ext hx.aeval_repr
end repr
end AlgebraicIndependent
variable (R)
def IsTranscendenceBasis (x : ι → A) : Prop :=
  AlgebraicIndependent R x ∧
    ∀ (s : Set A) (_ : AlgebraicIndependent R ((↑) : s → A)) (_ : range x ≤ s), range x = s