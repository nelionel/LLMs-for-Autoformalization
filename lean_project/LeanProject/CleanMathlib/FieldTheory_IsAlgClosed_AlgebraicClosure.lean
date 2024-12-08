import Mathlib.Algebra.DirectLimit
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.SplittingField.Construction
universe u v w
noncomputable section
open Polynomial
variable (k : Type u) [Field k]
namespace AlgebraicClosure
open MvPolynomial
abbrev MonicIrreducible : Type u :=
  { f : k[X] // Monic f ∧ Irreducible f }
def evalXSelf (f : MonicIrreducible k) : MvPolynomial (MonicIrreducible k) k :=
  Polynomial.eval₂ MvPolynomial.C (X f) f
def spanEval : Ideal (MvPolynomial (MonicIrreducible k) k) :=
  Ideal.span <| Set.range <| evalXSelf k
open Classical in
def toSplittingField (s : Finset (MonicIrreducible k)) :
    MvPolynomial (MonicIrreducible k) k →ₐ[k] SplittingField (∏ x ∈ s, x : k[X]) :=
  MvPolynomial.aeval fun f =>
    if hf : f ∈ s then
      rootOfSplits _
        ((splits_prod_iff _ fun (j : MonicIrreducible k) _ => j.2.2.ne_zero).1
          (SplittingField.splits _) f hf)
        (mt isUnit_iff_degree_eq_zero.2 f.2.2.not_unit)
    else 37
theorem toSplittingField_evalXSelf {s : Finset (MonicIrreducible k)} {f} (hf : f ∈ s) :
    toSplittingField k s (evalXSelf k f) = 0 := by
  rw [toSplittingField, evalXSelf, ← AlgHom.coe_toRingHom, hom_eval₂, AlgHom.coe_toRingHom,
    MvPolynomial.aeval_X, dif_pos hf, ← MvPolynomial.algebraMap_eq, AlgHom.comp_algebraMap]
  exact map_rootOfSplits _ _ _
theorem spanEval_ne_top : spanEval k ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one, spanEval, Ideal.span, ← Set.image_univ,
    Finsupp.mem_span_image_iff_linearCombination]
  rintro ⟨v, _, hv⟩
  replace hv := congr_arg (toSplittingField k v.support) hv
  rw [map_one, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finset.sum_eq_zero] at hv
  · exact zero_ne_one hv
  intro j hj
  rw [smul_eq_mul, map_mul, toSplittingField_evalXSelf _ (s := v.support) hj,
    mul_zero]
def maxIdeal : Ideal (MvPolynomial (MonicIrreducible k) k) :=
  Classical.choose <| Ideal.exists_le_maximal _ <| spanEval_ne_top k
instance maxIdeal.isMaximal : (maxIdeal k).IsMaximal :=
  (Classical.choose_spec <| Ideal.exists_le_maximal _ <| spanEval_ne_top k).1
theorem le_maxIdeal : spanEval k ≤ maxIdeal k :=
  (Classical.choose_spec <| Ideal.exists_le_maximal _ <| spanEval_ne_top k).2
def AdjoinMonic : Type u :=
  MvPolynomial (MonicIrreducible k) k ⧸ maxIdeal k
instance AdjoinMonic.field : Field (AdjoinMonic k) :=
  Ideal.Quotient.field _
instance AdjoinMonic.inhabited : Inhabited (AdjoinMonic k) :=
  ⟨37⟩
def toAdjoinMonic : k →+* AdjoinMonic k :=
  (Ideal.Quotient.mk _).comp C
instance AdjoinMonic.algebra : Algebra k (AdjoinMonic k) :=
  (toAdjoinMonic k).toAlgebra
theorem AdjoinMonic.algebraMap : algebraMap k (AdjoinMonic k) = (Ideal.Quotient.mk _).comp
    (C : k →+* MvPolynomial (MonicIrreducible k) k) := rfl
theorem AdjoinMonic.isIntegral (z : AdjoinMonic k) : IsIntegral k z := by
  let ⟨p, hp⟩ := Ideal.Quotient.mk_surjective z
  rw [← hp]
  induction p using MvPolynomial.induction_on generalizing z with
    | h_C => exact isIntegral_algebraMap
    | h_add _ _ ha hb => exact (ha _ rfl).add (hb _ rfl)
    | h_X p f ih =>
      refine @IsIntegral.mul k _ _ _ _ _ (Ideal.Quotient.mk (maxIdeal k) _) (ih _ rfl) ?_
      refine ⟨f, f.2.1, ?_⟩
      erw [AdjoinMonic.algebraMap, ← hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
      exact le_maxIdeal k (Ideal.subset_span ⟨f, rfl⟩)
theorem AdjoinMonic.exists_root {f : k[X]} (hfm : f.Monic) (hfi : Irreducible f) :
    ∃ x : AdjoinMonic k, f.eval₂ (toAdjoinMonic k) x = 0 :=
  ⟨Ideal.Quotient.mk _ <| X (⟨f, hfm, hfi⟩ : MonicIrreducible k), by
    erw [toAdjoinMonic, ← hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact le_maxIdeal k (Ideal.subset_span <| ⟨_, rfl⟩)⟩
def stepAux (n : ℕ) : Σ α : Type u, Field α :=
  Nat.recOn n ⟨k, inferInstance⟩ fun _ ih => ⟨@AdjoinMonic ih.1 ih.2, @AdjoinMonic.field ih.1 ih.2⟩
def Step (n : ℕ) : Type u :=
  (stepAux k n).1
theorem Step.zero : Step k 0 = k := rfl
instance Step.field (n : ℕ) : Field (Step k n) :=
  (stepAux k n).2
theorem Step.succ (n : ℕ) : Step k (n + 1) = AdjoinMonic (Step k n) := rfl
instance Step.inhabited (n) : Inhabited (Step k n) :=
  ⟨37⟩
def toStepZero : k →+* Step k 0 :=
  RingHom.id k
def toStepSucc (n : ℕ) : Step k n →+* (Step k (n + 1)) :=
  @toAdjoinMonic (Step k n) (Step.field k n)
instance Step.algebraSucc (n) : Algebra (Step k n) (Step k (n + 1)) :=
  (toStepSucc k n).toAlgebra
theorem toStepSucc.exists_root {n} {f : Polynomial (Step k n)} (hfm : f.Monic)
    (hfi : Irreducible f) : ∃ x : Step k (n + 1), f.eval₂ (toStepSucc k n) x = 0 :=
  @AdjoinMonic.exists_root _ (Step.field k n) _ hfm hfi
private def toStepOfLE' (m n : ℕ) (h : m ≤ n) : Step k m → Step k n :=
Nat.leRecOn h @fun a => toStepSucc k a
private theorem toStepOfLE'.succ (m n : ℕ) (h : m ≤ n) :
    toStepOfLE' k m (Nat.succ n) (h.trans n.le_succ) =
    (toStepSucc k n) ∘ toStepOfLE' k m n h := by
  ext x
  exact Nat.leRecOn_succ h x
def toStepOfLE (m n : ℕ) (h : m ≤ n) : Step k m →+* Step k n where
  toFun := toStepOfLE' k m n h
  map_one' := by
    induction' h with a h ih
    · exact Nat.leRecOn_self 1
    · simp [toStepOfLE'.succ k m a h, ih]
  map_mul' x y := by
    simp only
    induction' h with a h ih
    · simp_rw [toStepOfLE', Nat.leRecOn_self]
    · simp [toStepOfLE'.succ k m a h, ih]
  map_zero' := by
    simp only
    induction' h with a h ih
    · exact Nat.leRecOn_self 0
    · simp [toStepOfLE'.succ k m a h, ih]
  map_add' x y := by
    simp only
    induction' h with a h ih
    · simp_rw [toStepOfLE', Nat.leRecOn_self]
    · simp [toStepOfLE'.succ k m a h, ih]
@[simp]
theorem coe_toStepOfLE (m n : ℕ) (h : m ≤ n) :
    (toStepOfLE k m n h : Step k m → Step k n) = Nat.leRecOn h @fun n => toStepSucc k n :=
  rfl
instance Step.algebra (n) : Algebra k (Step k n) :=
  (toStepOfLE k 0 n n.zero_le).toAlgebra
instance Step.scalar_tower (n) : IsScalarTower k (Step k n) (Step k (n + 1)) :=
  IsScalarTower.of_algebraMap_eq fun z =>
    @Nat.leRecOn_succ (Step k) 0 n n.zero_le (n + 1).zero_le (@fun n => toStepSucc k n) z
private theorem toStepOfLE.succ (n : ℕ) (h : 0 ≤ n) :
    toStepOfLE k 0 (n + 1) (h.trans n.le_succ) =
    (toStepSucc k n).comp (toStepOfLE k 0 n h) := by
    ext1 x
    rw [RingHom.comp_apply]
    simp only [toStepOfLE, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change _ = (_ ∘ _) x
    rw [toStepOfLE'.succ k 0 n h]
theorem Step.isIntegral (n) : ∀ z : Step k n, IsIntegral k z := by
  induction' n with a h
  · intro z
    exact isIntegral_algebraMap
  · intro z
    change RingHom.IsIntegralElem _ _
    revert z
    change RingHom.IsIntegral _
    unfold algebraMap
    unfold Algebra.toRingHom
    unfold algebra
    unfold RingHom.toAlgebra
    unfold RingHom.toAlgebra'
    simp only
    rw [toStepOfLE.succ k a a.zero_le]
    apply @RingHom.IsIntegral.trans (Step k 0) (Step k a) (Step k (a + 1)) _ _ _
        (toStepOfLE k 0 a (a.zero_le : 0 ≤ a)) (toStepSucc k a) _
    · intro z
      convert AdjoinMonic.isIntegral (Step k a) (z : Step k (a + 1))
    · convert h 
instance toStepOfLE.directedSystem : DirectedSystem (Step k) fun i j h => toStepOfLE k i j h :=
  ⟨fun _ => Nat.leRecOn_self, fun _ _ _ h₁₂ h₂₃ x => (Nat.leRecOn_trans h₁₂ h₂₃ x).symm⟩
end AlgebraicClosure
def AlgebraicClosureAux [Field k] : Type u :=
  Ring.DirectLimit (AlgebraicClosure.Step k) fun i j h => AlgebraicClosure.toStepOfLE k i j h
namespace AlgebraicClosureAux
open AlgebraicClosure
local instance field : Field (AlgebraicClosureAux k) :=
  Field.DirectLimit.field _ _
instance : Inhabited (AlgebraicClosureAux k) :=
  ⟨37⟩
def ofStep (n : ℕ) : Step k n →+* AlgebraicClosureAux k :=
  Ring.DirectLimit.of _ _ _
theorem ofStep_succ (n : ℕ) : (ofStep k (n + 1)).comp (toStepSucc k n) = ofStep k n := by
  ext x
  have hx : toStepOfLE' k n (n+1) n.le_succ x = toStepSucc k n x := Nat.leRecOn_succ' x
  unfold ofStep
  rw [RingHom.comp_apply]
  dsimp [toStepOfLE]
  rw [← hx]
  change Ring.DirectLimit.of (Step k) (toStepOfLE' k) (n + 1) (_) =
      Ring.DirectLimit.of (Step k) (toStepOfLE' k) n x
  convert Ring.DirectLimit.of_f n.le_succ x
theorem exists_ofStep (z : AlgebraicClosureAux k) : ∃ n x, ofStep k n x = z :=
  Ring.DirectLimit.exists_of z
theorem exists_root {f : Polynomial (AlgebraicClosureAux k)}
    (hfm : f.Monic) (hfi : Irreducible f) : ∃ x : AlgebraicClosureAux k, f.eval x = 0 := by
  have : ∃ n p, Polynomial.map (ofStep k n) p = f := by
    convert Ring.DirectLimit.Polynomial.exists_of f
  obtain ⟨n, p, rfl⟩ := this
  rw [monic_map_iff] at hfm
  have := hfm.irreducible_of_irreducible_map (ofStep k n) p hfi
  obtain ⟨x, hx⟩ := toStepSucc.exists_root k hfm this
  refine ⟨ofStep k (n + 1) x, ?_⟩
  rw [← ofStep_succ k n, eval_map, ← hom_eval₂, hx, RingHom.map_zero]
@[local instance] theorem instIsAlgClosed : IsAlgClosed (AlgebraicClosureAux k) :=
  IsAlgClosed.of_exists_root _ fun _ => exists_root k
local instance instAlgebra : Algebra k (AlgebraicClosureAux k) :=
  (ofStep k 0).toAlgebra
def ofStepHom (n) : Step k n →ₐ[k] AlgebraicClosureAux k :=
  { ofStep k n with
    commutes' := by
      intro x
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
      convert @Ring.DirectLimit.of_f ℕ _ (Step k) _ (fun m n h => (toStepOfLE k m n h : _ → _))
          0 n n.zero_le x }
instance isAlgebraic : Algebra.IsAlgebraic k (AlgebraicClosureAux k) :=
  ⟨fun z =>
    IsIntegral.isAlgebraic <|
      let ⟨n, x, hx⟩ := exists_ofStep k z
      hx ▸ (Step.isIntegral k n x).map (ofStepHom k n)⟩
@[local instance] theorem isAlgClosure : IsAlgClosure k (AlgebraicClosureAux k) :=
  ⟨AlgebraicClosureAux.instIsAlgClosed k, isAlgebraic k⟩
end AlgebraicClosureAux
attribute [local instance] AlgebraicClosureAux.field AlgebraicClosureAux.instAlgebra
  AlgebraicClosureAux.instIsAlgClosed
@[stacks 09GT]
def AlgebraicClosure : Type u :=
  MvPolynomial (AlgebraicClosureAux k) k ⧸
    RingHom.ker (MvPolynomial.aeval (R := k) id).toRingHom
namespace AlgebraicClosure
instance instCommRing : CommRing (AlgebraicClosure k) := Ideal.Quotient.commRing _
instance instInhabited : Inhabited (AlgebraicClosure k) := ⟨37⟩
instance {S : Type*} [DistribSMul S k] [IsScalarTower S k k] : SMul S (AlgebraicClosure k) :=
  Submodule.Quotient.instSMul' _
instance instAlgebra {R : Type*} [CommSemiring R] [Algebra R k] : Algebra R (AlgebraicClosure k) :=
  Ideal.Quotient.algebra _
instance {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Algebra S k] [Algebra R k]
    [IsScalarTower R S k] : IsScalarTower R S (AlgebraicClosure k) :=
  Ideal.Quotient.isScalarTower _ _ _
def algEquivAlgebraicClosureAux :
    AlgebraicClosure k ≃ₐ[k] AlgebraicClosureAux k := by
  delta AlgebraicClosure
  exact Ideal.quotientKerAlgEquivOfSurjective
    (fun x => ⟨MvPolynomial.X x, by simp⟩)
instance instGroupWithZero : GroupWithZero (AlgebraicClosure k) :=
  let e := algEquivAlgebraicClosureAux k
  { inv := fun a ↦ e.symm (e a)⁻¹
    inv_zero := by simp
    mul_inv_cancel := fun a ha ↦ e.injective <| by simp [EmbeddingLike.map_ne_zero_iff.2 ha]
    __ := e.surjective.nontrivial }
instance instField : Field (AlgebraicClosure k) where
  __ := instCommRing _
  __ := instGroupWithZero _
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast q := algebraMap k _ q
  ratCast q := algebraMap k _ q
  nnratCast_def q := by change algebraMap k _ _ = _; simp_rw [NNRat.cast_def, map_div₀, map_natCast]
  ratCast_def q := by
    change algebraMap k _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
  nnqsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' <| by
    ext; simp [MvPolynomial.algebraMap_eq, NNRat.smul_def]
  qsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' <| by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]
instance isAlgClosed : IsAlgClosed (AlgebraicClosure k) :=
  IsAlgClosed.of_ringEquiv _ _ (algEquivAlgebraicClosureAux k).symm.toRingEquiv
instance : IsAlgClosure k (AlgebraicClosure k) := by
  rw [isAlgClosure_iff]
  exact ⟨inferInstance, (algEquivAlgebraicClosureAux k).symm.isAlgebraic⟩
instance isAlgebraic : Algebra.IsAlgebraic k (AlgebraicClosure k) :=
  IsAlgClosure.isAlgebraic
instance [CharZero k] : CharZero (AlgebraicClosure k) :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap k (AlgebraicClosure k)))
instance {p : ℕ} [CharP k p] : CharP (AlgebraicClosure k) p :=
  charP_of_injective_algebraMap (RingHom.injective (algebraMap k (AlgebraicClosure k))) p
instance {L : Type*} [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] :
    IsAlgClosure k (AlgebraicClosure L) where
  isAlgebraic := .trans (L := L)
  isAlgClosed := inferInstance
end AlgebraicClosure
theorem Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] {f g : K[X]} (hf0 : f ≠ 0) :
    (∀ x, IsRoot f x → IsRoot g x) ↔ f ∣ f.derivative * g := by
  refine ⟨?_, isRoot_of_isRoot_of_dvd_derivative_mul hf0⟩
  by_cases hg0 : g = 0
  · simp [hg0]
  by_cases hdf0 : derivative f = 0
  · rw [eq_C_of_derivative_eq_zero hdf0]
    simp only [eval_C, derivative_C, zero_mul, dvd_zero, implies_true]
  have hdg :  f.derivative * g ≠ 0 := mul_ne_zero hdf0 hg0
  classical rw [Splits.dvd_iff_roots_le_roots (IsAlgClosed.splits f) hf0 hdg, Multiset.le_iff_count]
  simp only [count_roots, rootMultiplicity_mul hdg]
  refine forall_imp fun a => ?_
  by_cases haf : f.eval a = 0
  · have h0 : 0 < f.rootMultiplicity a := (rootMultiplicity_pos hf0).2 haf
    rw [derivative_rootMultiplicity_of_root haf]
    intro h
    calc rootMultiplicity a f
        = rootMultiplicity a f - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.1 h0)).symm
      _ ≤ rootMultiplicity a f - 1 + rootMultiplicity a g := add_le_add le_rfl (Nat.succ_le_iff.1
        ((rootMultiplicity_pos hg0).2 (h haf)))
  · simp [haf, rootMultiplicity_eq_zero haf]