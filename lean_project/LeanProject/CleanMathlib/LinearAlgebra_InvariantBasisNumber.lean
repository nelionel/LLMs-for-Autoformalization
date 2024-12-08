import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.OrzechProperty
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Finsupp.Pi
noncomputable section
open Function
universe u v w
section
variable (R : Type u) [Semiring R]
@[mk_iff]
class StrongRankCondition : Prop where
  le_of_fin_injective : ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Injective f → n ≤ m
theorem le_of_fin_injective [StrongRankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R) :
    Injective f → n ≤ m :=
  StrongRankCondition.le_of_fin_injective f
theorem strongRankCondition_iff_succ :
    StrongRankCondition R ↔
      ∀ (n : ℕ) (f : (Fin (n + 1) → R) →ₗ[R] Fin n → R), ¬Function.Injective f := by
  refine ⟨fun h n => fun f hf => ?_, fun h => ⟨@fun n m f hf => ?_⟩⟩
  · letI : StrongRankCondition R := h
    exact Nat.not_succ_le_self n (le_of_fin_injective R f hf)
  · by_contra H
    exact
      h m (f.comp (Function.ExtendByZero.linearMap R (Fin.castLE (not_le.1 H))))
        (hf.comp (Function.extend_injective (Fin.strictMono_castLE _).injective _))
instance (priority := 100) strongRankCondition_of_orzechProperty
    [Nontrivial R] [OrzechProperty R] : StrongRankCondition R := by
  refine (strongRankCondition_iff_succ R).2 fun n i hi ↦ ?_
  let f : (Fin (n + 1) → R) →ₗ[R] Fin n → R := {
    toFun := fun x ↦ x ∘ Fin.castSucc
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
  }
  have h : (0 : Fin (n + 1) → R) = update (0 : Fin (n + 1) → R) (Fin.last n) 1 := by
    apply OrzechProperty.injective_of_surjective_of_injective i f hi
      (Fin.castSucc_injective _).surjective_comp_right
    ext m
    simp [f, update_apply, (Fin.castSucc_lt_last m).ne]
  simpa using congr_fun h (Fin.last n)
theorem card_le_of_injective [StrongRankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α → R) →ₗ[R] β → R) (i : Injective f) : Fintype.card α ≤ Fintype.card β := by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact
    le_of_fin_injective R ((Q.symm.toLinearMap.comp f).comp P.toLinearMap)
      (((LinearEquiv.symm Q).injective.comp i).comp (LinearEquiv.injective P))
theorem card_le_of_injective' [StrongRankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α →₀ R) →ₗ[R] β →₀ R) (i : Injective f) : Fintype.card α ≤ Fintype.card β := by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact
    card_le_of_injective R ((P.toLinearMap.comp f).comp Q.toLinearMap)
      ((P.injective.comp i).comp Q.injective)
class RankCondition : Prop where
  le_of_fin_surjective : ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Surjective f → m ≤ n
theorem le_of_fin_surjective [RankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R) :
    Surjective f → m ≤ n :=
  RankCondition.le_of_fin_surjective f
theorem card_le_of_surjective [RankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α → R) →ₗ[R] β → R) (i : Surjective f) : Fintype.card β ≤ Fintype.card α := by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact
    le_of_fin_surjective R ((Q.symm.toLinearMap.comp f).comp P.toLinearMap)
      (((LinearEquiv.symm Q).surjective.comp i).comp (LinearEquiv.surjective P))
theorem card_le_of_surjective' [RankCondition R] {α β : Type*} [Fintype α] [Fintype β]
    (f : (α →₀ R) →ₗ[R] β →₀ R) (i : Surjective f) : Fintype.card β ≤ Fintype.card α := by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact
    card_le_of_surjective R ((P.toLinearMap.comp f).comp Q.toLinearMap)
      ((P.surjective.comp i).comp Q.surjective)
instance (priority := 100) rankCondition_of_strongRankCondition [StrongRankCondition R] :
    RankCondition R where
  le_of_fin_surjective f s :=
    le_of_fin_injective R _ (f.splittingOfFunOnFintypeSurjective_injective s)
class InvariantBasisNumber : Prop where
  eq_of_fin_equiv : ∀ {n m : ℕ}, ((Fin n → R) ≃ₗ[R] Fin m → R) → n = m
instance (priority := 100) invariantBasisNumber_of_rankCondition [RankCondition R] :
    InvariantBasisNumber R where
  eq_of_fin_equiv e := le_antisymm (le_of_fin_surjective R e.symm.toLinearMap e.symm.surjective)
    (le_of_fin_surjective R e.toLinearMap e.surjective)
end
section
variable (R : Type u) [Semiring R] [InvariantBasisNumber R]
theorem eq_of_fin_equiv {n m : ℕ} : ((Fin n → R) ≃ₗ[R] Fin m → R) → n = m :=
  InvariantBasisNumber.eq_of_fin_equiv
theorem card_eq_of_linearEquiv {α β : Type*} [Fintype α] [Fintype β] (f : (α → R) ≃ₗ[R] β → R) :
    Fintype.card α = Fintype.card β :=
  eq_of_fin_equiv R
    ((LinearEquiv.funCongrLeft R R (Fintype.equivFin α)).trans f ≪≫ₗ
      (LinearEquiv.funCongrLeft R R (Fintype.equivFin β)).symm)
theorem nontrivial_of_invariantBasisNumber : Nontrivial R := by
  by_contra h
  refine zero_ne_one (eq_of_fin_equiv R ?_)
  haveI := not_nontrivial_iff_subsingleton.1 h
  haveI : Subsingleton (Fin 1 → R) :=
    Subsingleton.intro fun a b => funext fun x => Subsingleton.elim _ _
  exact
    { toFun := 0
      invFun := 0
      map_add' := by aesop
      map_smul' := by aesop
      left_inv := fun _ => by simp [eq_iff_true_of_subsingleton]
      right_inv := fun _ => by simp [eq_iff_true_of_subsingleton] }
end
section
variable (R : Type u) [Ring R] [Nontrivial R] [IsNoetherianRing R]
instance (priority := 100) IsNoetherianRing.strongRankCondition : StrongRankCondition R :=
  inferInstance
end
section
variable {R : Type u} [CommRing R] (I : Ideal R) {ι : Type v} [Fintype ι] {ι' : Type w}
private def induced_map (I : Ideal R) (e : (ι → R) →ₗ[R] ι' → R) :
    (ι → R) ⧸ I.pi ι → (ι' → R) ⧸ I.pi ι' := fun x =>
  Quotient.liftOn' x (fun y => Ideal.Quotient.mk (I.pi ι') (e y))
    (by
      refine fun a b hab => Ideal.Quotient.eq.2 fun h => ?_
      rw [Submodule.quotientRel_def] at hab
      rw [← LinearMap.map_sub]
      exact Ideal.map_pi _ _ hab e h)
private def induced_equiv [Fintype ι'] (I : Ideal R) (e : (ι → R) ≃ₗ[R] ι' → R) :
    ((ι → R) ⧸ I.pi ι) ≃ₗ[R ⧸ I] (ι' → R) ⧸ I.pi ι' where
  toFun := induced_map I e
  invFun := induced_map I e.symm
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    convert_to Ideal.Quotient.mk (I.pi ι') _ = Ideal.Quotient.mk (I.pi ι') _
    congr
    simp only [map_add]
  map_smul' := by
    rintro ⟨a⟩ ⟨b⟩
    convert_to Ideal.Quotient.mk (I.pi ι') _ = Ideal.Quotient.mk (I.pi ι') _
    congr
    simp only [LinearEquiv.coe_coe, LinearEquiv.map_smulₛₗ, RingHom.id_apply]
  left_inv := by
    rintro ⟨a⟩
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    congr
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨a⟩
    convert_to Ideal.Quotient.mk (I.pi ι') _ = Ideal.Quotient.mk (I.pi ι') _
    congr
    simp only [LinearEquiv.coe_coe,  LinearEquiv.apply_symm_apply]
end
section
attribute [local instance] Ideal.Quotient.field
instance (priority := 100) invariantBasisNumber_of_nontrivial_of_commRing {R : Type u} [CommRing R]
    [Nontrivial R] : InvariantBasisNumber R :=
  ⟨fun e =>
    let ⟨I, _hI⟩ := Ideal.exists_maximal R
    eq_of_fin_equiv (R ⧸ I)
      ((Ideal.piQuotEquiv _ _).symm ≪≫ₗ (induced_equiv _ e ≪≫ₗ Ideal.piQuotEquiv _ _))⟩
end