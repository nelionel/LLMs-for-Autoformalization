import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.PurelyInseparable
import Mathlib.LinearAlgebra.FreeAlgebra
import Mathlib.Order.Interval.Set.WithBotTop
import Mathlib.Order.DirectedInverseSystem
open Cardinal Module.Free Set Order IntermediateField InverseSystem
universe u v
variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
namespace Field.Emb
namespace Cardinal
noncomputable section
set_option quotPrecheck false
local notation "ι" => (Module.rank F E).ord.toType
private local instance : SuccOrder ι := SuccOrder.ofLinearWellFoundedLT ι
local notation i"⁺" => succ i 
def wellOrderedBasis : Basis ι F E :=
  (chooseBasis F E).reindex
    (Cardinal.eq.mp <| (mk_ord_toType _).trans <| rank_eq_card_chooseBasisIndex F E).some.symm
local notation "b" => wellOrderedBasis F E
local notation "Ē" => AlgebraicClosure E
variable {F E}
theorem adjoin_basis_eq_top : adjoin F (range b) = ⊤ :=
  toSubalgebra_injective <| Subalgebra.toSubmodule_injective <| top_unique <|
    (Basis.span_eq b).ge.trans <| (Algebra.span_le_adjoin F _).trans <| algebra_adjoin_le_adjoin _ _
section Algebraic
variable [rank_inf : Fact (ℵ₀ ≤ Module.rank F E)]
lemma noMaxOrder_rank_toType : NoMaxOrder ι := Cardinal.noMaxOrder Fact.out
attribute [local instance] noMaxOrder_rank_toType
open _root_.Algebra (IsAlgebraic)
variable [IsAlgebraic F E]
variable (F E) in
def leastExt : ι → ι :=
  wellFounded_lt.fix fun i ih ↦
    let s := range fun j : Iio i ↦ b (ih j j.2)
    wellFounded_lt.min {k | b k ∉ adjoin F s} <| by
      rw [← compl_setOf, nonempty_compl]; by_contra!
      simp_rw [eq_univ_iff_forall, mem_setOf] at this
      have := adjoin_le_iff.mpr (range_subset_iff.mpr this)
      rw [adjoin_basis_eq_top, ← eq_top_iff] at this
      apply_fun Module.rank F at this
      refine ne_of_lt ?_ this
      conv_rhs => rw [topEquiv.toLinearEquiv.rank_eq]
      have := mk_Iio_ord_toType i
      obtain eq | lt := rank_inf.out.eq_or_lt
      · replace this := mk_lt_aleph0_iff.mp (this.trans_eq eq.symm)
        have : FiniteDimensional F (adjoin F s) :=
          finiteDimensional_adjoin fun x _ ↦ (IsAlgebraic.isAlgebraic x).isIntegral
        exact (Module.rank_lt_aleph0 _ _).trans_eq eq
      · exact (Subalgebra.equivOfEq _ _ <| adjoin_algebraic_toSubalgebra
          fun x _ ↦ IsAlgebraic.isAlgebraic x)|>.toLinearEquiv.rank_eq.trans_lt <|
          (Algebra.rank_adjoin_le _).trans_lt (max_lt (mk_range_le.trans_lt this) lt)
local notation "φ" => leastExt F E
section
local notation "E⟮<"i"⟯" => adjoin F (b ∘ φ '' Iio i)
theorem isLeast_leastExt (i : ι) : IsLeast {k | b k ∉ E⟮<i⟯} (φ i) := by
  rw [image_eq_range, leastExt, wellFounded_lt.fix_eq]
  exact ⟨wellFounded_lt.min_mem _ _, fun _ ↦ (wellFounded_lt.min_le ·)⟩
theorem strictMono_leastExt : StrictMono φ := fun i j h ↦ by
  have least := isLeast_leastExt (F := F) (E := E)
  by_contra!
  obtain eq | lt := this.eq_or_lt
  · exact (least j).1 (subset_adjoin _ _ ⟨i, h, congr_arg b eq.symm⟩)
  · refine ((least i).2 <| mt (adjoin.mono _ _ _ (image_mono ?_) ·) (least j).1).not_lt lt
    exact fun k (hk : k < i) ↦ hk.trans h
theorem adjoin_image_leastExt (i : ι) : E⟮<i⟯ = adjoin F (b '' Iio (φ i)) := by
  refine le_antisymm (adjoin.mono _ _ _ ?_) (adjoin_le_iff.mpr ?_)
  · rw [image_comp]; apply image_mono; rintro _ ⟨j, hj, rfl⟩; exact strictMono_leastExt hj
  · rintro _ ⟨j, hj, rfl⟩; contrapose! hj; exact ((isLeast_leastExt i).2 hj).not_lt
theorem iSup_adjoin_eq_top : ⨆ i : ι, E⟮<i⟯ = ⊤ := by
  simp_rw [adjoin_image_leastExt, eq_top_iff, ← adjoin_basis_eq_top, adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  refine le_iSup (α := IntermediateField F E) _ (i⁺) (subset_adjoin _ _ ⟨i, ?_, rfl⟩)
  exact (lt_succ i).trans_le strictMono_leastExt.le_apply
theorem strictMono_filtration : StrictMono (E⟮<·⟯) :=
  fun i _ h ↦ ⟨adjoin.mono _ _ _ (image_mono <| Iio_subset_Iio h.le),
    fun incl ↦ (isLeast_leastExt i).1 (incl <| subset_adjoin _ _ ⟨i, h, rfl⟩)⟩
theorem filtration_succ (i : ι) : E⟮<i⁺⟯ = E⟮<i⟯⟮b (φ i)⟯.restrictScalars F := by
  rw [Iio_succ, ← Iio_insert, image_insert_eq, ← union_singleton, adjoin_adjoin_left]; rfl
local notation "X" i => Field.Emb (E⟮<i⟯) <| E⟮<i⟯⟮b (φ i)⟯
def succEquiv (i : ι) : (E⟮<i⁺⟯ →ₐ[F] Ē) ≃ (E⟮<i⟯ →ₐ[F] Ē) × X i :=
  (((show _ ≃ₐ[F] E⟮<i⟯⟮b (φ i)⟯ from equivOfEq (filtration_succ i))).arrowCongr .refl).trans <|
    algHomEquivSigma (B := E⟮<i⟯).trans <| .sigmaEquivProdOfEquiv fun _ ↦
      (@Field.embEquivOfIsAlgClosed _ _ _ _ _ _ _ (_) <|
        (Algebra.IsAlgebraic.tower_top (K := F) _).of_injective (val _) Subtype.val_injective).symm
theorem succEquiv_coherence (i : ι) (f) : (succEquiv i f).1 =
    f.comp (Subalgebra.inclusion <| strictMono_filtration.monotone <| le_succ i) := by
  ext; simp [succEquiv]; rfl 
instance (i : ι) : FiniteDimensional (E⟮<i⟯) (E⟮<i⟯⟮b (φ i)⟯) :=
  adjoin.finiteDimensional ((Algebra.IsAlgebraic.tower_top (K := F) _).isAlgebraic _).isIntegral
theorem deg_lt_aleph0 (i : ι) : #(X i) < ℵ₀ :=
  (toNat_ne_zero.mp (Field.instNeZeroFinSepDegree (E⟮<i⟯) <| E⟮<i⟯⟮b (φ i)⟯).out).2
open WithTop in
@[simps!] def filtration : WithTop ι ↪o IntermediateField F E :=
  .ofStrictMono (fun i ↦ i.recTopCoe ⊤ (E⟮<·⟯)) fun i j h ↦ by
    cases j
    · obtain ⟨i, rfl⟩ := ne_top_iff_exists.mp h.ne
      exact ⟨le_top, fun incl ↦ (isLeast_leastExt i).1 (incl trivial)⟩
    · obtain ⟨i, rfl⟩ := ne_top_iff_exists.mp (h.trans <| coe_lt_top _).ne
      exact strictMono_filtration (coe_lt_coe.mp h)
def factor (i : WithTop ι) : Type _ := i.recTopCoe PUnit (X ·)
variable [Algebra.IsSeparable F E]
instance (i : ι) : Algebra.IsSeparable (E⟮<i⟯) (E⟮<i⟯⟮b (φ i)⟯) :=
  have := Algebra.isSeparable_tower_top_of_isSeparable F (E⟮<i⟯) E
  have : IsScalarTower (E⟮<i⟯) (E⟮<i⟯⟮b (φ i)⟯) E := .of_algebraMap_eq' rfl
  Algebra.isSeparable_tower_bot_of_isSeparable _ _ E
open Field in
theorem two_le_deg (i : ι) : 2 ≤ #(X i) := by
  rw [← Nat.cast_eq_ofNat, ← toNat_le_iff_le_of_lt_aleph0 (nat_lt_aleph0 _) (deg_lt_aleph0 i),
    toNat_natCast, ← Nat.card, ← finSepDegree, finSepDegree_eq_finrank_of_isSeparable, Nat.succ_le]
  by_contra!
  obtain ⟨x, hx⟩ := finrank_adjoin_simple_eq_one_iff.mp (this.antisymm Module.finrank_pos)
  refine (isLeast_leastExt i).1 (hx ▸ ?_)
  exact x.2
end
local notation "E⟮<"i"⟯" => filtration i
variable (F E) in
def embFunctor ⦃i j : WithTop ι⦄ (h : i ≤ j) (f : E⟮<j⟯ →ₐ[F] Ē) : E⟮<i⟯ →ₐ[F] Ē :=
  f.comp (Subalgebra.inclusion <| filtration.monotone h)
instance : InverseSystem (embFunctor F E) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl
private local instance (i : ι) : Decidable (succ i = i) := .isFalse (lt_succ i).ne'
def equivSucc (i : WithTop ι) : (E⟮<i⁺⟯ →ₐ[F] Ē) ≃ (E⟮<i⟯ →ₐ[F] Ē) × factor i :=
  i.recTopCoe (((equivOfEq <| by rw [succ_top]).arrowCongr .refl).trans <| .symm <| .prodPUnit _)
    (succEquiv ·)
theorem equivSucc_coherence (i f) : (equivSucc i f).1 = embFunctor F E (le_succ i) f := by
  cases i; exacts [rfl, succEquiv_coherence _ f]
section Lim
variable {i : WithTop (Module.rank F E).ord.toType} 
theorem directed_filtration : Directed (· ≤ ·) fun j : Iio i ↦ filtration j.1 :=
  (filtration.monotone.comp <| Subtype.mono_coe _).directed_le
variable (hi : IsSuccPrelimit i)
include hi
open WithTop in
theorem iSup_filtration : ⨆ j : Iio i, filtration j = filtration i := by
  cases i
  · rw [← range_coe, iSup_range']; exact iSup_adjoin_eq_top
  refine (iSup_le fun j ↦ filtration.monotone (mem_Iio.1 j.2).le).antisymm (adjoin_le_iff.2 ?_)
  rintro _ ⟨j, hj, rfl⟩
  refine le_iSup (α := IntermediateField F E) _ ⟨j⁺, ?_⟩ (subset_adjoin F _ ?_)
  exacts [⟨j, lt_succ j, rfl⟩, hi.succ_lt (coe_lt_coe.mpr hj)]
open WithTop
lemma eq_bot_of_not_nonempty (hi : ¬ Nonempty (Iio i)) : filtration i = ⊥ := by
  cases i
  · have := mk_ne_zero_iff.mp (rank_pos.trans_eq (mk_ord_toType <| Module.rank F E).symm).ne'
    rw [← range_coe] at hi; exact (hi inferInstance).elim
  · exact bot_unique <| adjoin_le_iff.mpr fun _ ⟨j, hj, _⟩ ↦ (hi ⟨j, coe_lt_coe.mpr hj⟩).elim
open Classical in
def equivLim : (E⟮<i⟯ →ₐ[F] Ē) ≃ limit (embFunctor F E) i where
  toFun f := ⟨fun j ↦ embFunctor _ _ (id j.2 : j < i).le f, fun _ _ _ ↦ rfl⟩
  invFun f := if h : Nonempty (Iio i) then
    Subalgebra.iSupLift _ directed_filtration f.1
      (fun _ _ h ↦ (f.2 <| filtration.map_rel_iff.mp h).symm) _ <| by
        rw [← iSup_filtration hi, toSubalgebra_iSup_of_directed directed_filtration]
    else (Algebra.ofId F Ē).comp ((equivOfEq (eq_bot_of_not_nonempty hi h)).trans <| botEquiv F E)
  left_inv f := by
    split_ifs with h
    · ext ⟨x, hx⟩
      rw [← iSup_filtration hi, mem_toSubalgebra, ← SetLike.mem_coe,
          coe_iSup_of_directed directed_filtration, mem_iUnion] at hx
      rw [Subalgebra.iSupLift_of_mem _ _ (by exact hx.choose_spec)]; rfl
    · apply AlgHom.ext
      rw [((equivOfEq (eq_bot_of_not_nonempty hi h)).trans <| botEquiv F E).forall_congr_left]
      simp
  right_inv f := Subtype.ext <| funext fun j ↦ by
    have := Nonempty.intro j
    simp_rw [dif_pos this]
    apply Subalgebra.iSupLift_comp_inclusion
theorem equivLim_coherence (x l) : (equivLim hi x).1 l = embFunctor F E (mem_Iio.mp l.2).le x :=
  rfl
end Lim
def embEquivPi : Field.Emb F E ≃ ∀ i : ι, factor (F := F) (E := E) i :=
  let e := globalEquiv
    (fun i _ ↦ ⟨_, equivSucc_coherence i⟩) (fun _ hi ↦ ⟨equivLim hi, fun _ _ ↦ rfl⟩) ⊤
  (topEquiv.arrowCongr .refl).symm.trans <| e.trans <| .trans (.piCongrSet WithTop.range_coe.symm)
    <| .symm <| .piCongr (.ofInjective _ WithTop.coe_injective) fun _ ↦ .refl _
end Algebraic
end
end Cardinal
variable {F E}
theorem cardinal_eq_two_pow_rank [Algebra.IsSeparable F E]
    (rank_inf : ℵ₀ ≤ Module.rank F E) : #(Field.Emb F E) = 2 ^ Module.rank F E := by
  haveI := Fact.mk rank_inf
  rw [Emb.Cardinal.embEquivPi.cardinal_eq, mk_pi]
  apply le_antisymm
  · rw [← power_eq_two_power rank_inf (nat_lt_aleph0 2).le rank_inf]
    conv_rhs => rw [← mk_ord_toType (Module.rank F E), ← prod_const']
    exact prod_le_prod _ _ fun i ↦ (Emb.Cardinal.deg_lt_aleph0 _).le
  · conv_lhs => rw [← mk_ord_toType (Module.rank F E), ← prod_const']
    exact prod_le_prod _ _ Emb.Cardinal.two_le_deg
theorem cardinal_eq_of_isSeparable [Algebra.IsSeparable F E] :
    #(Field.Emb F E) = (fun c ↦ if ℵ₀ ≤ c then 2 ^ c else c) (Module.rank F E) := by
  dsimp only; split_ifs with h
  · exact cardinal_eq_two_pow_rank h
  rw [not_le, ← IsNoetherian.iff_rank_lt_aleph0] at h
  rw [← Module.finrank_eq_rank, ← toNat_eq_iff Module.finrank_pos.ne',
    ← Nat.card, ← finSepDegree, finSepDegree_eq_finrank_of_isSeparable]
theorem cardinal_eq_two_pow_sepDegree [Algebra.IsAlgebraic F E]
    (rank_inf : ℵ₀ ≤ sepDegree F E) : #(Field.Emb F E) = 2 ^ sepDegree F E := by
  rw [← cardinal_separableClosure, cardinal_eq_two_pow_rank rank_inf]
  rfl
theorem cardinal_eq [Algebra.IsAlgebraic F E] :
    #(Field.Emb F E) = (fun c ↦ if ℵ₀ ≤ c then 2 ^ c else c) (sepDegree F E) := by
  rw [← cardinal_separableClosure, cardinal_eq_of_isSeparable]; rfl
end Field.Emb