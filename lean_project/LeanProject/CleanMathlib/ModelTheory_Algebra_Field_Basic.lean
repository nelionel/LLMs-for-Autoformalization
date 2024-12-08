import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Data.Nat.Cast.Order.Ring
variable {K : Type*}
namespace FirstOrder
namespace Field
open Language Ring Structure BoundedFormula
inductive FieldAxiom : Type
  | addAssoc : FieldAxiom
  | zeroAdd : FieldAxiom
  | negAddCancel : FieldAxiom
  | mulAssoc : FieldAxiom
  | mulComm : FieldAxiom
  | oneMul : FieldAxiom
  | existsInv : FieldAxiom
  | leftDistrib : FieldAxiom
  | existsPairNE : FieldAxiom
@[simp]
def FieldAxiom.toSentence : FieldAxiom → Language.ring.Sentence
  | .addAssoc => ∀' ∀' ∀' (((&0 + &1) + &2) =' (&0 + (&1 + &2)))
  | .zeroAdd => ∀' (((0 : Language.ring.Term _) + &0) =' &0)
  | .negAddCancel => ∀' ∀' ((-&0 + &0) =' 0)
  | .mulAssoc => ∀' ∀' ∀' (((&0 * &1) * &2) =' (&0 * (&1 * &2)))
  | .mulComm => ∀' ∀' ((&0 * &1) =' (&1 * &0))
  | .oneMul => ∀' (((1 : Language.ring.Term _) * &0) =' &0)
  | .existsInv => ∀' (∼(&0 =' 0) ⟹ ∃' ((&0 * &1) =' 1))
  | .leftDistrib => ∀' ∀' ∀' ((&0 * (&1 + &2)) =' ((&0 * &1) + (&0 * &2)))
  | .existsPairNE => ∃' ∃' (∼(&0 =' &1))
@[simp]
def FieldAxiom.toProp (K : Type*) [Add K] [Mul K] [Neg K] [Zero K] [One K] :
    FieldAxiom → Prop
  | .addAssoc => ∀ x y z : K, (x + y) + z = x + (y + z)
  | .zeroAdd => ∀ x : K, 0 + x = x
  | .negAddCancel => ∀ x : K, -x + x = 0
  | .mulAssoc => ∀ x y z : K, (x * y) * z = x * (y * z)
  | .mulComm => ∀ x y : K, x * y = y * x
  | .oneMul => ∀ x : K, 1 * x = x
  | .existsInv => ∀ x : K, x ≠ 0 → ∃ y, x * y = 1
  | .leftDistrib => ∀ x y z : K, x * (y + z) = x * y + x * z
  | .existsPairNE => ∃ x y : K, x ≠ y
def _root_.FirstOrder.Language.Theory.field : Language.ring.Theory :=
  Set.range FieldAxiom.toSentence
theorem FieldAxiom.realize_toSentence_iff_toProp {K : Type*}
    [Add K] [Mul K] [Neg K] [Zero K] [One K] [CompatibleRing K]
    (ax : FieldAxiom) :
    (K ⊨ (ax.toSentence : Sentence Language.ring)) ↔ ax.toProp K := by
  cases ax <;>
  simp [Sentence.Realize, Formula.Realize, Fin.snoc]
theorem FieldAxiom.toProp_of_model {K : Type*}
    [Add K] [Mul K] [Neg K] [Zero K] [One K] [CompatibleRing K]
    [Theory.field.Model K] (ax : FieldAxiom) : ax.toProp K :=
  (FieldAxiom.realize_toSentence_iff_toProp ax).1
    (Theory.realize_sentence_of_mem Theory.field
      (Set.mem_range_self ax))
open FieldAxiom
noncomputable abbrev fieldOfModelField (K : Type*) [Language.ring.Structure K]
    [Theory.field.Model K] : Field K :=
  letI : DecidableEq K := Classical.decEq K
  letI := addOfRingStructure K
  letI := mulOfRingStructure K
  letI := negOfRingStructure K
  letI := zeroOfRingStructure K
  letI := oneOfRingStructure K
  letI := compatibleRingOfRingStructure K
  have exists_inv : ∀ x : K, x ≠ 0 → ∃ y : K, x * y = 1 :=
    existsInv.toProp_of_model
  letI : Inv K := ⟨fun x => if hx0 : x = 0 then 0 else Classical.choose (exists_inv x hx0)⟩
  Field.ofMinimalAxioms K
    addAssoc.toProp_of_model
    zeroAdd.toProp_of_model
    negAddCancel.toProp_of_model
    mulAssoc.toProp_of_model
    mulComm.toProp_of_model
    oneMul.toProp_of_model
    (fun x hx0 => show x * (dite _ _ _) = _ from
        (dif_neg hx0).symm ▸ Classical.choose_spec (existsInv.toProp_of_model x hx0))
    (dif_pos rfl)
    leftDistrib.toProp_of_model
    existsPairNE.toProp_of_model
section
attribute [local instance] fieldOfModelField
noncomputable abbrev compatibleRingOfModelField (K : Type*) [Language.ring.Structure K]
    [Theory.field.Model K] : CompatibleRing K :=
  compatibleRingOfRingStructure K
end
instance [Field K] [CompatibleRing K] : Theory.field.Model K :=
  { realize_of_mem := by
      simp only [Theory.field, Set.mem_range, exists_imp]
      rintro φ a rfl
      rw [a.realize_toSentence_iff_toProp (K := K)]
      cases a with
      | existsPairNE => exact exists_pair_ne K
      | existsInv => exact fun x hx0 => ⟨x⁻¹, mul_inv_cancel₀ hx0⟩
      | addAssoc => exact add_assoc
      | zeroAdd => exact zero_add
      | negAddCancel => exact neg_add_cancel
      | mulAssoc => exact mul_assoc
      | mulComm => exact mul_comm
      | oneMul => exact one_mul
      | leftDistrib => exact mul_add }
end Field
end FirstOrder