import Mathlib.Analysis.NormedSpace.OperatorNorm.Completeness
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
open NNReal ENNReal ContinuousLinearMap MulOpposite
universe u v
structure DoubleCentralizer (𝕜 : Type u) (A : Type v) [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] extends
    (A →L[𝕜] A) × (A →L[𝕜] A) where
  central : ∀ x y : A, snd x * y = x * fst y
@[inherit_doc]
scoped[MultiplierAlgebra] notation "𝓜(" 𝕜 ", " A ")" => DoubleCentralizer 𝕜 A
open MultiplierAlgebra
@[ext]
lemma DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
    (a b : 𝓜(𝕜, A)) (h : a.toProd = b.toProd) : a = b := by
  cases a
  cases b
  simpa using h
namespace DoubleCentralizer
section NontriviallyNormed
variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
variable {𝕜 A}
theorem range_toProd :
    Set.range toProd = { lr : (A →L[𝕜] A) × (A →L[𝕜] A) | ∀ x y, lr.2 x * y = x * lr.1 y } :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
instance instAdd : Add 𝓜(𝕜, A) where
  add a b :=
    { toProd := a.toProd + b.toProd
      central := fun x y =>
        show (a.snd + b.snd) x * y = x * (a.fst + b.fst) y by
          simp only [ContinuousLinearMap.add_apply, mul_add, add_mul, central] }
instance instZero : Zero 𝓜(𝕜, A) where
  zero :=
    { toProd := 0
      central := fun x y => (zero_mul y).trans (mul_zero x).symm }
instance instNeg : Neg 𝓜(𝕜, A) where
  neg a :=
    { toProd := -a.toProd
      central := fun x y =>
        show -a.snd x * y = x * -a.fst y by
          simp only [ContinuousLinearMap.neg_apply, neg_mul, mul_neg, central] }
instance instSub : Sub 𝓜(𝕜, A) where
  sub a b :=
    { toProd := a.toProd - b.toProd
      central := fun x y =>
        show (a.snd - b.snd) x * y = x * (a.fst - b.fst) y by
          simp only [ContinuousLinearMap.sub_apply, _root_.sub_mul, _root_.mul_sub, central] }
section Scalars
variable {S : Type*} [Monoid S] [DistribMulAction S A] [SMulCommClass 𝕜 S A]
  [ContinuousConstSMul S A] [IsScalarTower S A A] [SMulCommClass S A A]
instance instSMul : SMul S 𝓜(𝕜, A) where
  smul s a :=
    { toProd := s • a.toProd
      central := fun x y =>
        show (s • a.snd) x * y = x * (s • a.fst) y by
          simp only [ContinuousLinearMap.smul_apply, mul_smul_comm, smul_mul_assoc, central] }
@[simp]
theorem smul_toProd (s : S) (a : 𝓜(𝕜, A)) : (s • a).toProd = s • a.toProd :=
  rfl
theorem smul_fst (s : S) (a : 𝓜(𝕜, A)) : (s • a).fst = s • a.fst :=
  rfl
theorem smul_snd (s : S) (a : 𝓜(𝕜, A)) : (s • a).snd = s • a.snd :=
  rfl
variable {T : Type*} [Monoid T] [DistribMulAction T A] [SMulCommClass 𝕜 T A]
  [ContinuousConstSMul T A] [IsScalarTower T A A] [SMulCommClass T A A]
instance instIsScalarTower [SMul S T] [IsScalarTower S T A] : IsScalarTower S T 𝓜(𝕜, A) where
  smul_assoc _ _ a := ext (𝕜 := 𝕜) (A := A) _ _ <| smul_assoc _ _ a.toProd
instance instSMulCommClass [SMulCommClass S T A] : SMulCommClass S T 𝓜(𝕜, A) where
  smul_comm _ _ a := ext (𝕜 := 𝕜) (A := A) _ _ <| smul_comm _ _ a.toProd
instance instIsCentralScalar {R : Type*} [Semiring R] [Module R A] [SMulCommClass 𝕜 R A]
    [ContinuousConstSMul R A] [IsScalarTower R A A] [SMulCommClass R A A] [Module Rᵐᵒᵖ A]
    [IsCentralScalar R A] : IsCentralScalar R 𝓜(𝕜, A) where
  op_smul_eq_smul _ a := ext (𝕜 := 𝕜) (A := A) _ _ <| op_smul_eq_smul _ a.toProd
end Scalars
instance instOne : One 𝓜(𝕜, A) :=
  ⟨⟨1, fun _x _y => rfl⟩⟩
instance instMul : Mul 𝓜(𝕜, A) where
  mul a b :=
    { toProd := (a.fst.comp b.fst, b.snd.comp a.snd)
      central := fun x y => show b.snd (a.snd x) * y = x * a.fst (b.fst y) by simp only [central] }
instance instNatCast : NatCast 𝓜(𝕜, A) where
  natCast n :=
    ⟨n, fun x y => by
      rw [Prod.snd_natCast, Prod.fst_natCast]
      simp only [← Nat.smul_one_eq_cast, smul_apply, one_apply, mul_smul_comm, smul_mul_assoc]⟩
instance instIntCast : IntCast 𝓜(𝕜, A) where
  intCast n :=
    ⟨n, fun x y => by
      rw [Prod.snd_intCast, Prod.fst_intCast]
      simp only [← Int.smul_one_eq_cast, smul_apply, one_apply, mul_smul_comm, smul_mul_assoc]⟩
instance instPow : Pow 𝓜(𝕜, A) ℕ where
  pow a n :=
    ⟨a.toProd ^ n, fun x y => by
      induction' n with k hk generalizing x y
      · rfl
      · rw [Prod.pow_snd, Prod.pow_fst] at hk ⊢
        rw [pow_succ' a.snd, mul_apply, a.central, hk, pow_succ a.fst, mul_apply]⟩
instance instInhabited : Inhabited 𝓜(𝕜, A) :=
  ⟨0⟩
@[simp]
theorem add_toProd (a b : 𝓜(𝕜, A)) : (a + b).toProd = a.toProd + b.toProd :=
  rfl
@[simp]
theorem zero_toProd : (0 : 𝓜(𝕜, A)).toProd = 0 :=
  rfl
@[simp]
theorem neg_toProd (a : 𝓜(𝕜, A)) : (-a).toProd = -a.toProd :=
  rfl
@[simp]
theorem sub_toProd (a b : 𝓜(𝕜, A)) : (a - b).toProd = a.toProd - b.toProd :=
  rfl
@[simp]
theorem one_toProd : (1 : 𝓜(𝕜, A)).toProd = 1 :=
  rfl
@[simp]
theorem natCast_toProd (n : ℕ) : (n : 𝓜(𝕜, A)).toProd = n :=
  rfl
@[deprecated (since := "2024-04-17")]
alias nat_cast_toProd := natCast_toProd
@[simp]
theorem intCast_toProd (n : ℤ) : (n : 𝓜(𝕜, A)).toProd = n :=
  rfl
@[deprecated (since := "2024-04-17")]
alias int_cast_toProd := intCast_toProd
@[simp]
theorem pow_toProd (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).toProd = a.toProd ^ n :=
  rfl
theorem add_fst (a b : 𝓜(𝕜, A)) : (a + b).fst = a.fst + b.fst :=
  rfl
theorem add_snd (a b : 𝓜(𝕜, A)) : (a + b).snd = a.snd + b.snd :=
  rfl
theorem zero_fst : (0 : 𝓜(𝕜, A)).fst = 0 :=
  rfl
theorem zero_snd : (0 : 𝓜(𝕜, A)).snd = 0 :=
  rfl
theorem neg_fst (a : 𝓜(𝕜, A)) : (-a).fst = -a.fst :=
  rfl
theorem neg_snd (a : 𝓜(𝕜, A)) : (-a).snd = -a.snd :=
  rfl
theorem sub_fst (a b : 𝓜(𝕜, A)) : (a - b).fst = a.fst - b.fst :=
  rfl
theorem sub_snd (a b : 𝓜(𝕜, A)) : (a - b).snd = a.snd - b.snd :=
  rfl
theorem one_fst : (1 : 𝓜(𝕜, A)).fst = 1 :=
  rfl
theorem one_snd : (1 : 𝓜(𝕜, A)).snd = 1 :=
  rfl
@[simp]
theorem mul_fst (a b : 𝓜(𝕜, A)) : (a * b).fst = a.fst * b.fst :=
  rfl
@[simp]
theorem mul_snd (a b : 𝓜(𝕜, A)) : (a * b).snd = b.snd * a.snd :=
  rfl
theorem natCast_fst (n : ℕ) : (n : 𝓜(𝕜, A)).fst = n :=
  rfl
@[deprecated (since := "2024-04-17")]
alias nat_cast_fst := natCast_fst
theorem natCast_snd (n : ℕ) : (n : 𝓜(𝕜, A)).snd = n :=
  rfl
@[deprecated (since := "2024-04-17")]
alias nat_cast_snd := natCast_snd
theorem intCast_fst (n : ℤ) : (n : 𝓜(𝕜, A)).fst = n :=
  rfl
@[deprecated (since := "2024-04-17")]
alias int_cast_fst := intCast_fst
theorem intCast_snd (n : ℤ) : (n : 𝓜(𝕜, A)).snd = n :=
  rfl
@[deprecated (since := "2024-04-17")]
alias int_cast_snd := intCast_snd
theorem pow_fst (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).fst = a.fst ^ n :=
  rfl
theorem pow_snd (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).snd = a.snd ^ n :=
  rfl
def toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ := fun a =>
  (a.fst, MulOpposite.op a.snd)
theorem toProdMulOpposite_injective :
    Function.Injective (toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ) :=
  fun _a _b h =>
    let h' := Prod.ext_iff.mp h
    ext (𝕜 := 𝕜) (A := A) _ _ <| Prod.ext h'.1 <| MulOpposite.op_injective h'.2
theorem range_toProdMulOpposite :
    Set.range toProdMulOpposite =
      { lr : (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ | ∀ x y, unop lr.2 x * y = x * lr.1 y } :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨(x.1, unop x.2), hx⟩, Prod.ext rfl rfl⟩⟩
instance instRing : Ring 𝓜(𝕜, A) :=
  toProdMulOpposite_injective.ring _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_pow _ _) (fun _ => rfl) fun _ => rfl
@[simps]
def toProdHom : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A) where
  toFun := toProd
  map_zero' := rfl
  map_add' _x _y := rfl
@[simps]
def toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ where
  toFun := toProdMulOpposite
  map_zero' := rfl
  map_one' := rfl
  map_add' _x _y := rfl
  map_mul' _x _y := rfl
instance instModule {S : Type*} [Semiring S] [Module S A] [SMulCommClass 𝕜 S A]
    [ContinuousConstSMul S A] [IsScalarTower S A A] [SMulCommClass S A A] : Module S 𝓜(𝕜, A) :=
  Function.Injective.module S toProdHom (ext (𝕜 := 𝕜) (A := A)) fun _x _y => rfl
instance instAlgebra : Algebra 𝕜 𝓜(𝕜, A) where
  toFun k :=
    { toProd := algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A)) k
      central := fun x y => by
        simp_rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply,
          mul_smul_comm, smul_mul_assoc] }
  map_one' := ext (𝕜 := 𝕜) (A := A) _ _ <| map_one <| algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A))
  map_mul' _ _ :=
    ext (𝕜 := 𝕜) (A := A) _ _ <|
      Prod.ext (map_mul (algebraMap 𝕜 (A →L[𝕜] A)) _ _)
        ((map_mul (algebraMap 𝕜 (A →L[𝕜] A)) _ _).trans (Algebra.commutes _ _))
  map_zero' := ext (𝕜 := 𝕜) (A := A) _ _ <| map_zero <| algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A))
  map_add' _ _ := ext (𝕜 := 𝕜) (A := A) _ _ <|
    map_add (algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A))) _ _
  commutes' _ _ := ext (𝕜 := 𝕜) (A := A) _ _ <|
    Prod.ext (Algebra.commutes _ _) (Algebra.commutes _ _).symm
  smul_def' _ _ := ext (𝕜 := 𝕜) (A := A) _ _ <|
    Prod.ext (Algebra.smul_def _ _) ((Algebra.smul_def _ _).trans <| Algebra.commutes _ _)
@[simp]
theorem algebraMap_toProd (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).toProd = algebraMap 𝕜 _ k :=
  rfl
theorem algebraMap_fst (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).fst = algebraMap 𝕜 _ k :=
  rfl
theorem algebraMap_snd (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).snd = algebraMap 𝕜 _ k :=
  rfl
section Star
variable [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A]
instance instStar : Star 𝓜(𝕜, A) where
  star a :=
    { fst :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.snd).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)
      snd :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.fst).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)
      central := fun x y => by
        simpa only [star_mul, star_star] using (congr_arg star (a.central (star y) (star x))).symm }
@[simp]
theorem star_fst (a : 𝓜(𝕜, A)) (b : A) : (star a).fst b = star (a.snd (star b)) :=
  rfl
@[simp]
theorem star_snd (a : 𝓜(𝕜, A)) (b : A) : (star a).snd b = star (a.fst (star b)) :=
  rfl
instance instStarAddMonoid : StarAddMonoid 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStar with
    star_involutive := fun x => by ext <;> simp only [star_fst, star_snd, star_star]
    star_add := fun x y => by
      ext <;>
        simp only [star_fst, star_snd, add_fst, add_snd, ContinuousLinearMap.add_apply, star_add] }
instance instStarRing : StarRing 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStarAddMonoid with
    star_mul := fun a b => by
      ext <;>
        simp only [star_fst, star_snd, mul_fst, mul_snd, star_star, ContinuousLinearMap.coe_mul,
          Function.comp_apply] }
instance instStarModule : StarModule 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStarAddMonoid (𝕜 := 𝕜) (A := A) with
    star_smul := fun k a => by ext <;> exact star_smul _ _ }
end Star
variable (𝕜)
@[coe]
protected noncomputable def coe (a : A) : 𝓜(𝕜, A) :=
  { fst := ContinuousLinearMap.mul 𝕜 A a
    snd := (ContinuousLinearMap.mul 𝕜 A).flip a
    central := fun _x _y => mul_assoc _ _ _ }
variable {𝕜}
noncomputable instance : CoeTC A 𝓜(𝕜, A) where
  coe := DoubleCentralizer.coe 𝕜
@[simp, norm_cast]
theorem coe_fst (a : A) : (a : 𝓜(𝕜, A)).fst = ContinuousLinearMap.mul 𝕜 A a :=
  rfl
@[simp, norm_cast]
theorem coe_snd (a : A) : (a : 𝓜(𝕜, A)).snd = (ContinuousLinearMap.mul 𝕜 A).flip a :=
  rfl
theorem coe_eq_algebraMap : (DoubleCentralizer.coe 𝕜 : 𝕜 → 𝓜(𝕜, 𝕜)) = algebraMap 𝕜 𝓜(𝕜, 𝕜) := by
  ext x : 3
  · rfl 
  · refine ContinuousLinearMap.ext fun y => ?_
    exact mul_comm y x  
@[simps]
noncomputable def coeHom [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A] :
    A →⋆ₙₐ[𝕜] 𝓜(𝕜, A) where
  toFun a := a
  map_smul' _ _ := ext _ _ _ _ <| Prod.ext (map_smul _ _ _) (map_smul _ _ _)
  map_zero' := ext _ _ _ _ <| Prod.ext (map_zero _) (map_zero _)
  map_add' _ _ := ext _ _ _ _ <| Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_mul' _ _ := ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => (mul_assoc _ _ _))
    (ContinuousLinearMap.ext fun _ => (mul_assoc _ _ _).symm)
  map_star' _ := ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => (star_star_mul _ _).symm)
    (ContinuousLinearMap.ext fun _ => (star_mul_star _ _).symm)
noncomputable instance : NormedRing 𝓜(𝕜, A) :=
  NormedRing.induced _ _ (toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ)
    (by simpa using toProdMulOpposite_injective)
theorem norm_def (a : 𝓜(𝕜, A)) : ‖a‖ = ‖toProdHom a‖ :=
  rfl
theorem nnnorm_def (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖toProdHom a‖₊ :=
  rfl
theorem norm_def' (a : 𝓜(𝕜, A)) : ‖a‖ = ‖toProdMulOppositeHom a‖ :=
  rfl
theorem nnnorm_def' (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖toProdMulOppositeHom a‖₊ :=
  rfl
instance instNormedSpace : NormedSpace 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instModule with
    norm_smul_le := fun k a => (norm_smul_le k a.toProdMulOpposite : _) }
instance instNormedAlgebra : NormedAlgebra 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instAlgebra, DoubleCentralizer.instNormedSpace with }
theorem isUniformEmbedding_toProdMulOpposite :
    IsUniformEmbedding (toProdMulOpposite (𝕜 := 𝕜) (A := A)) :=
  isUniformEmbedding_comap toProdMulOpposite_injective
@[deprecated (since := "2024-10-01")]
alias uniformEmbedding_toProdMulOpposite := isUniformEmbedding_toProdMulOpposite
instance [CompleteSpace A] : CompleteSpace 𝓜(𝕜, A) := by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_toProdMulOpposite.isUniformInducing]
  apply IsClosed.isComplete
  simp only [range_toProdMulOpposite, Set.setOf_forall]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ ?_
  · exact
      ((ContinuousLinearMap.apply 𝕜 A _).continuous.comp <| continuous_unop.comp continuous_snd).mul
        continuous_const
  exact continuous_const.mul ((ContinuousLinearMap.apply 𝕜 A _).continuous.comp continuous_fst)
variable [StarRing A] [CStarRing A]
theorem norm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a.snd‖ := by
  have h0 : ∀ f : A →L[𝕜] A, ∀ C : ℝ≥0, (∀ b : A, ‖f b‖₊ ^ 2 ≤ C * ‖f b‖₊ * ‖b‖₊) → ‖f‖₊ ≤ C := by
    intro f C h
    have h1 : ∀ b, C * ‖f b‖₊ * ‖b‖₊ ≤ C * ‖f‖₊ * ‖b‖₊ ^ 2 := by
      intro b
      convert mul_le_mul_right' (mul_le_mul_left' (f.le_opNNNorm b) C) ‖b‖₊ using 1
      ring
    have := NNReal.div_le_of_le_mul <| f.opNNNorm_le_bound _ <| by
      simpa only [sqrt_sq, sqrt_mul] using fun b ↦ sqrt_le_sqrt.2 <| (h b).trans (h1 b)
    convert NNReal.rpow_le_rpow this two_pos.le
    · simp only [NNReal.rpow_two, div_pow, sq_sqrt]
      simp only [sq, mul_self_div_self]
    · simp only [NNReal.rpow_two, sq_sqrt]
  have h1 : ∀ b, ‖a.fst b‖₊ ^ 2 ≤ ‖a.snd‖₊ * ‖a.fst b‖₊ * ‖b‖₊ := by
    intro b
    calc
      ‖a.fst b‖₊ ^ 2 = ‖star (a.fst b) * a.fst b‖₊ := by
        simpa only [← sq] using CStarRing.nnnorm_star_mul_self.symm
      _ ≤ ‖a.snd (star (a.fst b))‖₊ * ‖b‖₊ := (a.central (star (a.fst b)) b ▸ nnnorm_mul_le _ _)
      _ ≤ ‖a.snd‖₊ * ‖a.fst b‖₊ * ‖b‖₊ :=
        nnnorm_star (a.fst b) ▸ mul_le_mul_right' (a.snd.le_opNNNorm _) _
  have h2 : ∀ b, ‖a.snd b‖₊ ^ 2 ≤ ‖a.fst‖₊ * ‖a.snd b‖₊ * ‖b‖₊ := by
    intro b
    calc
      ‖a.snd b‖₊ ^ 2 = ‖a.snd b * star (a.snd b)‖₊ := by
        simpa only [← sq] using CStarRing.nnnorm_self_mul_star.symm
      _ ≤ ‖b‖₊ * ‖a.fst (star (a.snd b))‖₊ :=
        ((a.central b (star (a.snd b))).symm ▸ nnnorm_mul_le _ _)
      _ = ‖a.fst (star (a.snd b))‖₊ * ‖b‖₊ := mul_comm _ _
      _ ≤ ‖a.fst‖₊ * ‖a.snd b‖₊ * ‖b‖₊ :=
        nnnorm_star (a.snd b) ▸ mul_le_mul_right' (a.fst.le_opNNNorm _) _
  exact le_antisymm (h0 _ _ h1) (h0 _ _ h2)
theorem nnnorm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a.snd‖₊ :=
  Subtype.ext <| norm_fst_eq_snd a
@[simp]
theorem norm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a‖ := by
  simp only [norm_def, toProdHom_apply, Prod.norm_def, norm_fst_eq_snd, max_eq_right le_rfl]
@[simp]
theorem norm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖ = ‖a‖ := by rw [← norm_fst, norm_fst_eq_snd]
@[simp]
theorem nnnorm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a‖₊ :=
  Subtype.ext (norm_fst a)
@[simp]
theorem nnnorm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖₊ = ‖a‖₊ :=
  Subtype.ext (norm_snd a)
end NontriviallyNormed
section DenselyNormed
variable {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜]
variable [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
variable [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [StarModule 𝕜 A]
instance instCStarRing : CStarRing 𝓜(𝕜, A) where
  norm_mul_self_le := fun (a : 𝓜(𝕜, A)) => le_of_eq <| Eq.symm <| congr_arg ((↑) : ℝ≥0 → ℝ) <|
    show ‖star a * a‖₊ = ‖a‖₊ * ‖a‖₊ by
      have hball : (Metric.closedBall (0 : A) 1).Nonempty :=
        Metric.nonempty_closedBall.2 zero_le_one
      have key :
        ∀ x y, ‖x‖₊ ≤ 1 → ‖y‖₊ ≤ 1 → ‖a.snd (star (a.fst (star x))) * y‖₊ ≤ ‖a‖₊ * ‖a‖₊ := by
        intro x y hx hy
        rw [a.central]
        calc
          ‖star (a.fst (star x)) * a.fst y‖₊ ≤ ‖a.fst (star x)‖₊ * ‖a.fst y‖₊ :=
            nnnorm_star (a.fst (star x)) ▸ nnnorm_mul_le _ _
          _ ≤ ‖a.fst‖₊ * 1 * (‖a.fst‖₊ * 1) :=
            (mul_le_mul' (a.fst.le_opNorm_of_le ((nnnorm_star x).trans_le hx))
              (a.fst.le_opNorm_of_le hy))
          _ ≤ ‖a‖₊ * ‖a‖₊ := by simp only [mul_one, nnnorm_fst, le_rfl]
      rw [← nnnorm_snd]
      simp only [mul_snd, ← sSup_closed_unit_ball_eq_nnnorm, star_snd, mul_apply]
      simp only [← @opNNNorm_mul_apply 𝕜 _ A]
      simp only [← sSup_closed_unit_ball_eq_nnnorm, mul_apply']
      refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (hball.image _) ?_ fun r hr => ?_
      · rintro - ⟨x, hx, rfl⟩
        refine csSup_le (hball.image _) ?_
        rintro - ⟨y, hy, rfl⟩
        exact key x y (mem_closedBall_zero_iff.1 hx) (mem_closedBall_zero_iff.1 hy)
      · simp only [Set.mem_image, Set.mem_setOf_eq, exists_prop, exists_exists_and_eq_and]
        have hr' : NNReal.sqrt r < ‖a‖₊ := ‖a‖₊.sqrt_mul_self ▸ NNReal.sqrt_lt_sqrt.2 hr
        simp_rw [← nnnorm_fst, ← sSup_closed_unit_ball_eq_nnnorm] at hr'
        obtain ⟨_, ⟨x, hx, rfl⟩, hxr⟩ := exists_lt_of_lt_csSup (hball.image _) hr'
        have hx' : ‖x‖₊ ≤ 1 := mem_closedBall_zero_iff.1 hx
        refine ⟨star x, mem_closedBall_zero_iff.2 ((nnnorm_star x).trans_le hx'), ?_⟩
        refine lt_csSup_of_lt ?_ ⟨x, hx, rfl⟩ ?_
        · refine ⟨‖a‖₊ * ‖a‖₊, ?_⟩
          rintro - ⟨y, hy, rfl⟩
          exact key (star x) y ((nnnorm_star x).trans_le hx') (mem_closedBall_zero_iff.1 hy)
        · simpa only [a.central, star_star, CStarRing.nnnorm_star_mul_self, NNReal.sq_sqrt, ← sq]
            using pow_lt_pow_left₀ hxr zero_le' two_ne_zero
end DenselyNormed
noncomputable instance {A : Type*} [NonUnitalCStarAlgebra A] : CStarAlgebra 𝓜(ℂ, A) where
end DoubleCentralizer