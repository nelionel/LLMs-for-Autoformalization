import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Quotient.Basic
universe u v
open TensorProduct DirectSum
namespace Module
variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
@[mk_iff] class FaithfullyFlat extends Module.Flat R M : Prop where
  submodule_ne_top : ∀ ⦃m : Ideal R⦄ (_ : Ideal.IsMaximal m), m • (⊤ : Submodule R M) ≠ ⊤
namespace FaithfullyFlat
instance self : FaithfullyFlat R R where
  submodule_ne_top m h r := Ideal.eq_top_iff_one _ |>.not.1 h.ne_top <| by
    simpa using show 1 ∈ (m • ⊤ : Ideal R) from r.symm ▸ ⟨⟩
section proper_ideal
lemma iff_flat_and_proper_ideal :
    FaithfullyFlat R M ↔
    (Flat R M ∧ ∀ (I : Ideal R), I ≠ ⊤ → I • (⊤ : Submodule R M) ≠ ⊤) := by
  rw [faithfullyFlat_iff]
  refine ⟨fun ⟨flat, h⟩ => ⟨flat, fun I hI r => ?_⟩, fun h => ⟨h.1, fun m hm => h.2 _ hm.ne_top⟩⟩
  obtain ⟨m, hm, le⟩ := I.exists_le_maximal hI
  exact h hm <| eq_top_iff.2 <| show ⊤ ≤ m • ⊤ from r ▸ Submodule.smul_mono le (by simp [r])
lemma iff_flat_and_ideal_smul_eq_top :
    FaithfullyFlat R M ↔
    (Flat R M ∧ ∀ (I : Ideal R), I • (⊤ : Submodule R M) = ⊤ → I = ⊤) :=
  iff_flat_and_proper_ideal R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun I => eq_iff_iff.2 <| by tauto
end proper_ideal
section faithful
instance rTensor_nontrivial
    [fl: FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Nontrivial N] :
    Nontrivial (N ⊗[R] M) := by
  obtain ⟨n, hn⟩ := nontrivial_iff_exists_ne (0 : N) |>.1 inferInstance
  let I := (Submodule.span R {n}).annihilator
  by_cases I_ne_top : I = ⊤
  · rw [Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul] at I_ne_top
    contradiction
  let inc : R ⧸ I →ₗ[R] N := Submodule.liftQ _ ((LinearMap.lsmul R N).flip n) <| fun r hr => by
    simpa only [LinearMap.mem_ker, LinearMap.flip_apply, LinearMap.lsmul_apply,
      Submodule.mem_annihilator_span_singleton, I] using hr
  have injective_inc : Function.Injective inc := LinearMap.ker_eq_bot.1 <| eq_bot_iff.2 <| by
    intro r hr
    induction r using Quotient.inductionOn' with | h r =>
    simpa only [Submodule.Quotient.mk''_eq_mk, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_annihilator_span_singleton, LinearMap.mem_ker, Submodule.liftQ_apply,
      LinearMap.flip_apply, LinearMap.lsmul_apply, I, inc] using hr
  have ne_top := iff_flat_and_proper_ideal R M |>.1 fl |>.2 I I_ne_top
  refine subsingleton_or_nontrivial _ |>.resolve_left fun rid => ?_
  exact False.elim <| ne_top <| Submodule.subsingleton_quotient_iff_eq_top.1 <|
    Function.Injective.comp (g := LinearMap.rTensor M inc)
      (fl.toFlat.rTensor_preserves_injective_linearMap inc injective_inc)
      ((quotTensorEquivQuotSMul M I).symm.injective) |>.subsingleton
instance lTensor_nontrivial
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Nontrivial N] :
    Nontrivial (M ⊗[R] N) :=
  TensorProduct.comm R M N |>.toEquiv.nontrivial
lemma rTensor_reflects_triviality
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N]
    [h : Subsingleton (N ⊗[R] M)] : Subsingleton N := by
  revert h; change _ → _; contrapose
  simp only [not_subsingleton_iff_nontrivial]
  intro h
  infer_instance
lemma lTensor_reflects_triviality
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N]
    [Subsingleton (M ⊗[R] N)] :
    Subsingleton N := by
  haveI : Subsingleton (N ⊗[R] M) := (TensorProduct.comm R N M).toEquiv.injective.subsingleton
  apply rTensor_reflects_triviality R M
attribute [-simp] Ideal.Quotient.mk_eq_mk in
lemma iff_flat_and_rTensor_faithful :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Nontrivial N → Nontrivial (N ⊗[R] M)) := by
  refine ⟨fun fl => ⟨inferInstance, rTensor_nontrivial R M⟩, fun ⟨flat, faithful⟩ => ⟨?_⟩⟩
  intro m hm rid
  specialize faithful (ULift (R ⧸ m)) inferInstance
  haveI : Nontrivial ((R ⧸ m) ⊗[R] M) :=
    (congr (ULift.moduleEquiv : ULift (R ⧸ m) ≃ₗ[R] R ⧸ m)
      (LinearEquiv.refl R M)).symm.toEquiv.nontrivial
  have := (quotTensorEquivQuotSMul M m).toEquiv.symm.nontrivial
  haveI H : Subsingleton (M ⧸ m • (⊤ : Submodule R M)) := by
    rwa [Submodule.subsingleton_quotient_iff_eq_top]
  rw [← not_nontrivial_iff_subsingleton] at H
  contradiction
lemma iff_flat_and_rTensor_reflects_triviality :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Subsingleton (N ⊗[R] M) → Subsingleton N) :=
  iff_flat_and_rTensor_faithful R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 <| by
      simp only [← not_subsingleton_iff_nontrivial]; tauto
lemma iff_flat_and_lTensor_faithful :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Nontrivial N → Nontrivial (M ⊗[R] N)) :=
  iff_flat_and_rTensor_faithful R M |>.trans
  ⟨fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).toEquiv.nontrivial⟩,
    fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).symm.toEquiv.nontrivial⟩⟩
lemma iff_flat_and_lTensor_reflects_triviality :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Subsingleton (M ⊗[R] N) → Subsingleton N) :=
  iff_flat_and_lTensor_faithful R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 <| by
      simp only [← not_subsingleton_iff_nontrivial]; tauto
end faithful
lemma of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] [FaithfullyFlat R M]
    (e : N ≃ₗ[R] M) : FaithfullyFlat R N := by
  rw [iff_flat_and_lTensor_faithful]
  exact ⟨Flat.of_linearEquiv R M N e,
    fun P _ _ hP ↦ (TensorProduct.congr e (LinearEquiv.refl R P)).toEquiv.nontrivial⟩
section
open Classical
instance directSum {ι : Type*} [Nonempty ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [∀ i, FaithfullyFlat R (M i)] : FaithfullyFlat R (⨁ i, M i) := by
  rw [iff_flat_and_lTensor_faithful]
  refine ⟨inferInstance, fun N _ _ hN ↦ ?_⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨x, y, hxy⟩ := Nontrivial.exists_pair_ne (α := M i ⊗[R] N)
  haveI : Nontrivial (⨁ (i : ι), M i ⊗[R] N) :=
    ⟨DirectSum.of _ i x, DirectSum.of _ i y, fun h ↦ hxy (DirectSum.of_injective i h)⟩
  apply (TensorProduct.directSumLeft R M N).toEquiv.nontrivial
instance finsupp (ι : Type v) [Nonempty ι] : FaithfullyFlat R (ι →₀ R) :=
  of_linearEquiv _ _ (finsuppLEquivDirectSum R R ι)
end
instance [Nontrivial M] [Module.Free R M] : FaithfullyFlat R M :=
  of_linearEquiv _ _ (Free.repr R M)
section exact
section arbitrary_universe
variable {N1 : Type*} [AddCommGroup N1] [Module R N1]
variable {N2 : Type*} [AddCommGroup N2] [Module R N2]
variable {N3 : Type*} [AddCommGroup N3] [Module R N3]
variable (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3)
lemma range_le_ker_of_exact_rTensor [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
    LinearMap.range l12 ≤ LinearMap.ker l23 := by
  rintro _ ⟨n1, rfl⟩
  rw [LinearMap.mem_ker]
  by_contra! hn1
  let E : Submodule R N3 := Submodule.span R {l23 (l12 n1)}
  have hE : Nontrivial E :=
    ⟨0, ⟨⟨l23 (l12 n1), Submodule.mem_span_singleton_self _⟩, Subtype.coe_ne_coe.1 hn1.symm⟩⟩
  have eq1 : ∀ (m : M), l23 (l12 n1) ⊗ₜ[R] m = 0 := fun m ↦
    ex.apply_apply_eq_zero (n1 ⊗ₜ[R] m)
  have eq0 : (⊤ : Submodule R (E ⊗[R] M)) = ⊥ := by
    ext x
    simp only [Submodule.mem_top, Submodule.mem_bot, true_iff]
    have mem : x ∈ (⊤ : Submodule R _) := ⟨⟩
    rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem
    obtain ⟨c, hc, rfl⟩ := mem
    choose b a hy using hc
    let r :  ⦃a : E ⊗[R] M⦄ → a ∈ ↑c.support → R := fun a ha =>
      Submodule.mem_span_singleton.1 (b ha).2 |>.choose
    have hr : ∀ ⦃i : E ⊗[R] M⦄ (hi : i ∈ c.support), b hi =
        r hi • ⟨l23 (l12 n1), Submodule.mem_span_singleton_self _⟩ := fun a ha =>
      Subtype.ext <| Submodule.mem_span_singleton.1 (b ha).2 |>.choose_spec.symm
    refine Finset.sum_eq_zero fun i hi => show c i • i = 0 from
      (Module.Flat.rTensor_preserves_injective_linearMap (M := M) E.subtype <|
              Submodule.injective_subtype E) ?_
    rw [← hy hi, hr hi, smul_tmul, map_smul, LinearMap.rTensor_tmul, Submodule.subtype_apply, eq1,
      smul_zero, map_zero]
  have : Subsingleton (E ⊗[R] M) := subsingleton_iff_forall_eq 0 |>.2 fun x =>
    show x ∈ (⊥ : Submodule R _) from eq0 ▸ ⟨⟩
  exact not_subsingleton_iff_nontrivial.2 inferInstance <| fl.rTensor_reflects_triviality R M E
lemma rTensor_reflects_exact [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
    Function.Exact l12 l23 := LinearMap.exact_iff.2 <| by
  have complex : LinearMap.range l12 ≤ LinearMap.ker l23 := range_le_ker_of_exact_rTensor R M _ _ ex
  let H := LinearMap.ker l23 ⧸ LinearMap.range (Submodule.inclusion complex)
  suffices triv_coh : Subsingleton H by
    rw [Submodule.subsingleton_quotient_iff_eq_top, Submodule.range_inclusion,
      Submodule.comap_subtype_eq_top] at triv_coh
    exact le_antisymm triv_coh complex
  suffices Subsingleton (H ⊗[R] M) from rTensor_reflects_triviality R M H
  let e : H ⊗[R] M ≃ₗ[R] _ := TensorProduct.quotientTensorEquiv _ _
  rw [e.toEquiv.subsingleton_congr, Submodule.subsingleton_quotient_iff_eq_top,
    LinearMap.range_eq_top]
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x m =>
    rcases x with ⟨x, (hx : l23 x = 0)⟩
    have mem : x ⊗ₜ[R] m ∈ LinearMap.ker (l23.rTensor M) := by simp [hx]
    rw [LinearMap.exact_iff.1 ex] at mem
    obtain ⟨y, hy⟩ := mem
    refine ⟨LinearMap.rTensor M (LinearMap.rangeRestrict _ ∘ₗ LinearMap.rangeRestrict l12) y,
      Module.Flat.rTensor_preserves_injective_linearMap (LinearMap.ker l23).subtype
      Subtype.val_injective ?_⟩
    simp only [LinearMap.comp_codRestrict, LinearMap.rTensor_tmul, Submodule.coe_subtype, ← hy]
    rw [← LinearMap.comp_apply]
    erw [← LinearMap.rTensor_comp]
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, LinearMap.comp_assoc,
      LinearMap.subtype_comp_codRestrict, ← LinearMap.comp_assoc, Submodule.subtype_comp_inclusion,
      LinearMap.subtype_comp_codRestrict]
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, by simp⟩
lemma lTensor_reflects_exact [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.lTensor M) (l23.lTensor M)) :
    Function.Exact l12 l23 :=
  rTensor_reflects_exact R M _ _ <| ex.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.comm _ _ _) (e₂ := TensorProduct.comm _ _ _)
    (e₃ := TensorProduct.comm _ _ _) (by ext; rfl) (by ext; rfl)
end arbitrary_universe
section fixed_universe
lemma exact_iff_rTensor_exact [fl : FaithfullyFlat R M]
    {N1 : Type max u v} [AddCommGroup N1] [Module R N1]
    {N2 : Type max u v} [AddCommGroup N2] [Module R N2]
    {N3 : Type max u v} [AddCommGroup N3] [Module R N3]
    (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3) :
    Function.Exact l12 l23 ↔ Function.Exact (l12.rTensor M) (l23.rTensor M) :=
  ⟨fun e => Module.Flat.iff_rTensor_exact.1 fl.toFlat e,
    fun ex => rTensor_reflects_exact R M l12 l23 ex⟩
lemma iff_exact_iff_rTensor_exact :
    FaithfullyFlat R M ↔
    (∀ {N1 : Type max u v} [AddCommGroup N1] [Module R N1]
      {N2 : Type max u v} [AddCommGroup N2] [Module R N2]
      {N3 : Type max u v} [AddCommGroup N3] [Module R N3]
      (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.rTensor M) (l23.rTensor M)) :=
  ⟨fun fl => exact_iff_rTensor_exact R M, fun iff_exact =>
    iff_flat_and_rTensor_reflects_triviality _ _ |>.2 ⟨Flat.iff_rTensor_exact.2 <| by aesop,
    fun N _ _ h => subsingleton_iff_forall_eq 0 |>.2 <| fun y => by
      simpa [eq_comm] using (iff_exact (0 : PUnit →ₗ[R] N) (0 : N →ₗ[R] PUnit) |>.2 fun x => by
        simpa using Subsingleton.elim _ _) y⟩⟩
lemma iff_exact_iff_lTensor_exact :
    FaithfullyFlat R M ↔
    (∀ {N1 : Type max u v} [AddCommGroup N1] [Module R N1]
      {N2 : Type max u v} [AddCommGroup N2] [Module R N2]
      {N3 : Type max u v} [AddCommGroup N3] [Module R N3]
      (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.lTensor M) (l23.lTensor M)) := by
  simp only [iff_exact_iff_rTensor_exact, LinearMap.rTensor_exact_iff_lTensor_exact]
end fixed_universe
end exact
section linearMap
section arbitrary_universe
lemma zero_iff_lTensor_zero [h: FaithfullyFlat R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') :
    f = 0 ↔ LinearMap.lTensor M f = 0 :=
  ⟨fun hf => hf.symm ▸ LinearMap.lTensor_zero M, fun hf => by
    have := lTensor_reflects_exact R M f LinearMap.id (by
      rw [LinearMap.exact_iff, hf, LinearMap.range_zero, LinearMap.ker_eq_bot]
      apply Module.Flat.lTensor_preserves_injective_linearMap
      exact fun _ _ h => h)
    ext x; simpa using this (f x)⟩
lemma zero_iff_rTensor_zero [h: FaithfullyFlat R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {N' : Type*} [AddCommGroup N'] [Module R N']
    (f : N →ₗ[R] N') :
    f = 0 ↔ LinearMap.rTensor M f = 0 :=
  zero_iff_lTensor_zero R M f |>.trans
  ⟨fun h => by ext n m; exact (TensorProduct.comm R N' M).injective <|
    (by simpa using congr($h (m ⊗ₜ n))), fun h => by
    ext m n; exact (TensorProduct.comm R M N').injective <| (by simpa using congr($h (n ⊗ₜ m)))⟩
end arbitrary_universe
section fixed_universe
lemma iff_zero_iff_lTensor_zero :
    FaithfullyFlat R M ↔
    (Module.Flat R M ∧
      (∀ {N : Type max u v} [AddCommGroup N] [Module R N]
        {N' : Type max u v} [AddCommGroup N'] [Module R N']
        (f : N →ₗ[R] N'), f.lTensor M = 0 ↔ f = 0)) :=
  ⟨fun fl => ⟨inferInstance, fun f => zero_iff_lTensor_zero R M f |>.symm⟩,
    fun ⟨flat, Z⟩ => iff_flat_and_lTensor_reflects_triviality R M |>.2 ⟨flat, fun N _ _ _ => by
      have := Z (LinearMap.id : N →ₗ[R] N) |>.1 (by ext; exact Subsingleton.elim _ _)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y => congr($this y)⟩⟩
lemma iff_zero_iff_rTensor_zero :
    FaithfullyFlat R M ↔
    (Module.Flat R M ∧
      (∀ {N : Type max u v} [AddCommGroup N] [Module R N]
        {N' : Type max u v} [AddCommGroup N'] [Module R N']
        (f : N →ₗ[R] N'), f.rTensor M = 0 ↔ (f = 0))) :=
  ⟨fun fl => ⟨inferInstance, fun f => zero_iff_rTensor_zero R M f |>.symm⟩,
    fun ⟨flat, Z⟩ => iff_flat_and_rTensor_reflects_triviality R M |>.2 ⟨flat, fun N _ _ _ => by
      have := Z (LinearMap.id : N →ₗ[R] N) |>.1 (by ext; exact Subsingleton.elim _ _)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y => congr($this y)⟩⟩
end fixed_universe
end linearMap
section trans
open TensorProduct LinearMap
variable (R : Type*) [CommRing R]
variable (S : Type*) [CommRing S] [Algebra R S]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [FaithfullyFlat R S] [FaithfullyFlat S M]
include S in
theorem trans : FaithfullyFlat R M := by
  rw [iff_zero_iff_lTensor_zero]
  refine ⟨Module.Flat.trans R S M, @fun N _ _ N' _ _ f => ⟨fun aux => ?_, fun eq => eq ▸ by simp⟩⟩
  rw [zero_iff_lTensor_zero (R:= R) (M := S) f,
    show f.lTensor S = (AlgebraTensorModule.map (A:= S) LinearMap.id f).restrictScalars R by aesop,
    show (0 :  S ⊗[R] N →ₗ[R] S ⊗[R] N') = (0 : S ⊗[R] N →ₗ[S] S ⊗[R] N').restrictScalars R by rfl,
    restrictScalars_inj, zero_iff_lTensor_zero (R:= S) (M := M)]
  ext m n
  apply_fun AlgebraTensorModule.cancelBaseChange R S S M N' using LinearEquiv.injective _
  simpa using congr($aux (m ⊗ₜ[R] n))
@[deprecated (since := "2024-11-08")] alias comp := trans
end trans
end FaithfullyFlat
end Module