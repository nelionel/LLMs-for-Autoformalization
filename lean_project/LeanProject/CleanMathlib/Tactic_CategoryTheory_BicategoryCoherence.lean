import Mathlib.CategoryTheory.Bicategory.Coherence
import Mathlib.Tactic.CategoryTheory.BicategoricalComp
noncomputable section
universe w v u
open CategoryTheory CategoryTheory.FreeBicategory
open scoped Bicategory
variable {B : Type u} [Bicategory.{w, v} B] {a b c d : B}
namespace Mathlib.Tactic.BicategoryCoherence
class LiftHom {a b : B} (f : a ⟶ b) where
  lift : of.obj a ⟶ of.obj b
instance liftHomId : LiftHom (𝟙 a) where lift := 𝟙 (of.obj a)
instance liftHomComp (f : a ⟶ b) (g : b ⟶ c) [LiftHom f] [LiftHom g] : LiftHom (f ≫ g) where
  lift := LiftHom.lift f ≫ LiftHom.lift g
instance (priority := 100) liftHomOf (f : a ⟶ b) : LiftHom f where lift := of.map f
class LiftHom₂ {f g : a ⟶ b} [LiftHom f] [LiftHom g] (η : f ⟶ g) where
  lift : LiftHom.lift f ⟶ LiftHom.lift g
instance liftHom₂Id (f : a ⟶ b) [LiftHom f] : LiftHom₂ (𝟙 f) where
  lift := 𝟙 _
instance liftHom₂LeftUnitorHom (f : a ⟶ b) [LiftHom f] : LiftHom₂ (λ_ f).hom where
  lift := (λ_ (LiftHom.lift f)).hom
instance liftHom₂LeftUnitorInv (f : a ⟶ b) [LiftHom f] : LiftHom₂ (λ_ f).inv where
  lift := (λ_ (LiftHom.lift f)).inv
instance liftHom₂RightUnitorHom (f : a ⟶ b) [LiftHom f] : LiftHom₂ (ρ_ f).hom where
  lift := (ρ_ (LiftHom.lift f)).hom
instance liftHom₂RightUnitorInv (f : a ⟶ b) [LiftHom f] : LiftHom₂ (ρ_ f).inv where
  lift := (ρ_ (LiftHom.lift f)).inv
instance liftHom₂AssociatorHom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g]
    [LiftHom h] : LiftHom₂ (α_ f g h).hom where
  lift := (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).hom
instance liftHom₂AssociatorInv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g]
    [LiftHom h] : LiftHom₂ (α_ f g h).inv where
  lift := (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).inv
instance liftHom₂Comp {f g h : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h] (η : f ⟶ g) (θ : g ⟶ h)
    [LiftHom₂ η] [LiftHom₂ θ] : LiftHom₂ (η ≫ θ) where
  lift := LiftHom₂.lift η ≫ LiftHom₂.lift θ
instance liftHom₂WhiskerLeft (f : a ⟶ b) [LiftHom f] {g h : b ⟶ c} (η : g ⟶ h) [LiftHom g]
    [LiftHom h] [LiftHom₂ η] : LiftHom₂ (f ◁ η) where
  lift := LiftHom.lift f ◁ LiftHom₂.lift η
instance liftHom₂WhiskerRight {f g : a ⟶ b} (η : f ⟶ g) [LiftHom f] [LiftHom g] [LiftHom₂ η]
    {h : b ⟶ c} [LiftHom h] : LiftHom₂ (η ▷ h) where
  lift := LiftHom₂.lift η ▷ LiftHom.lift h
open Lean Elab Tactic Meta
def exception {α : Type} (g : MVarId) (msg : MessageData) : MetaM α :=
  throwTacticEx `bicategorical_coherence g msg
def exception' (msg : MessageData) : TacticM Unit := do
  try
    liftMetaTactic (exception (msg := msg))
  catch _ =>
    throwError msg
set_option quotPrecheck false in
def mkLiftMap₂LiftExpr (e : Expr) : TermElabM Expr := do
  Term.elabTerm
    (← ``((FreeBicategory.lift (Prefunctor.id _)).map₂ (LiftHom₂.lift $(← Term.exprToSyntax e))))
    none
def bicategory_coherence (g : MVarId) : TermElabM Unit := g.withContext do
  withOptions (fun opts => synthInstance.maxSize.set opts
    (max 256 (synthInstance.maxSize.get opts))) do
  let thms := [``BicategoricalCoherence.iso, ``Iso.trans, ``Iso.symm, ``Iso.refl,
    ``Bicategory.whiskerRightIso, ``Bicategory.whiskerLeftIso].foldl
    (·.addDeclToUnfoldCore ·) {}
  let (ty, _) ← dsimp (← g.getType) (← Simp.mkContext (simpTheorems := #[thms]))
  let some (_, lhs, rhs) := (← whnfR ty).eq? | exception g "Not an equation of morphisms."
  let lift_lhs ← mkLiftMap₂LiftExpr lhs
  let lift_rhs ← mkLiftMap₂LiftExpr rhs
  let g₁ ← g.change (← mkEq lift_lhs lift_rhs)
  let [g₂] ← g₁.applyConst ``congrArg
    | exception g "congrArg failed in coherence"
  let [] ← g₂.applyConst ``Subsingleton.elim
    | exception g "This shouldn't happen; Subsingleton.elim does not create goals."
elab "bicategory_coherence" : tactic => do bicategory_coherence (← getMainGoal)
open Lean.Parser.Tactic
syntax (name := whisker_simps) "whisker_simps" optConfig : tactic
@[inherit_doc whisker_simps]
elab_rules : tactic
| `(tactic| whisker_simps $cfg) => do
  evalTactic (← `(tactic|
    simp $cfg only [Category.assoc,
      Bicategory.comp_whiskerLeft, Bicategory.id_whiskerLeft,
      Bicategory.whiskerRight_comp, Bicategory.whiskerRight_id,
      Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_id,
      Bicategory.comp_whiskerRight, Bicategory.id_whiskerRight, Bicategory.whisker_assoc]
    ))
@[nolint unusedArguments]
theorem assoc_liftHom₂ {f g h i : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h]
    (η : f ⟶ g) (θ : g ⟶ h) (ι : h ⟶ i) [LiftHom₂ η] [LiftHom₂ θ] : η ≫ θ ≫ ι = (η ≫ θ) ≫ ι :=
  (Category.assoc _ _ _).symm
end Mathlib.Tactic.BicategoryCoherence