import Mathlib.Lean.Expr.Basic
import Mathlib.Logic.Equiv.Defs
namespace Lean.Expr
open Lean Meta
inductive ProdTree where
  | type (tp : Expr) (l : Level)
  | prod (fst snd : ProdTree) (lfst lsnd : Level)
deriving Repr
def ProdTree.getType : ProdTree → Expr
  | type tp _ => tp
  | prod fst snd u v => mkAppN (.const ``Prod [u,v]) #[fst.getType, snd.getType]
def ProdTree.size : ProdTree → Nat
  | type _ _ => 1
  | prod fst snd _ _ => fst.size + snd.size
def ProdTree.components : ProdTree → List Expr
  | type tp _ => [tp]
  | prod fst snd _ _ => fst.components ++ snd.components
partial def mkProdTree (e : Expr) : MetaM ProdTree :=
  match e.consumeMData with
    | .app (.app (.const ``Prod [u,v]) X) Y => do
        return .prod (← X.mkProdTree) (← Y.mkProdTree) u v
    | X => do
      let some u := (← whnfD <| ← inferType X).type? | throwError "Not a type{indentExpr X}"
      return .type X u
def ProdTree.unpack (t : Expr) : ProdTree → MetaM (List Expr)
  | type _ _ => return [t]
  | prod fst snd u v => do
      let fst' ← fst.unpack <| mkAppN (.const ``Prod.fst [u,v]) #[fst.getType, snd.getType, t]
      let snd' ← snd.unpack <| mkAppN (.const ``Prod.snd [u,v]) #[fst.getType, snd.getType, t]
      return fst' ++ snd'
def ProdTree.pack (ts : List Expr) : ProdTree → MetaM Expr
  | type _ _ => do
    match ts with
      | [] => throwError "Can't pack the empty list."
      | [a] => return a
      | _ => throwError "Failed due to size mismatch."
  | prod fst snd u v => do
    let fstSize := fst.size
    let sndSize := snd.size
    unless ts.length == fstSize + sndSize do throwError "Failed due to size mismatch."
    let tsfst := ts.toArray[:fstSize] |>.toArray.toList
    let tssnd := ts.toArray[fstSize:] |>.toArray.toList
    let mk : Expr := mkAppN (.const ``Prod.mk [u,v]) #[fst.getType, snd.getType]
    return .app (.app mk (← fst.pack tsfst)) (← snd.pack tssnd)
def ProdTree.convertTo (P1 P2 : ProdTree) (e : Expr) : MetaM Expr :=
  return ← P2.pack <| ← P1.unpack e
def mkProdFun (a b : Expr) : MetaM Expr := do
  let pa ← a.mkProdTree
  let pb ← b.mkProdTree
  unless pa.components.length == pb.components.length do
    throwError "The number of components in{indentD a}\nand{indentD b}\nmust match."
  for (x,y) in pa.components.zip pb.components do
    unless ← isDefEq x y do
      throwError "Component{indentD x}\nis not definitionally equal to component{indentD y}."
  withLocalDeclD `t a fun fvar => do
    mkLambdaFVars #[fvar] (← pa.convertTo pb fvar)
def mkProdEquiv (a b : Expr) : MetaM Expr := do
  let some u := (← whnfD <| ← inferType a).type? | throwError "Not a type{indentExpr a}"
  let some v := (← whnfD <| ← inferType b).type? | throwError "Not a type{indentExpr b}"
  return mkAppN (.const ``Equiv.mk [.succ u,.succ v])
    #[a, b, ← mkProdFun a b, ← mkProdFun b a,
      .app (.const ``rfl [.succ u]) a,
      .app (.const ``rfl [.succ v]) b]
syntax (name := prodAssocStx) "prod_assoc_internal%" : term
open Elab Term in
@[term_elab prodAssocStx]
def elabProdAssoc : TermElab := fun stx expectedType? => do
  match stx with
  | `(prod_assoc_internal%) => do
    let some expectedType ← tryPostponeIfHasMVars? expectedType?
          | throwError "expected type must be known"
    let .app (.app (.const ``Equiv _) a) b := expectedType
          | throwError "Expected type{indentD expectedType}\nis not of the form `α ≃ β`."
    mkProdEquiv a b
  | _ => throwUnsupportedSyntax
macro "prod_assoc%" : term => `((prod_assoc_internal% : _ ≃ _))
end Lean.Expr