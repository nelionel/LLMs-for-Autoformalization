import Mathlib.Tactic.FunProp.StateList
import Mathlib.Algebra.Group.Pi.Basic
open Lean Meta
namespace Mathlib.Meta.FunProp.RefinedDiscrTree
inductive Key where
  | star : Nat → Key
  | opaque : Key
  | const : Name → Nat → Key
  | fvar : FVarId → Nat → Key
  | bvar : Nat → Nat → Key
  | lit : Literal → Key
  | sort : Key
  | lam : Key
  | forall : Key
  | proj : Name → Nat → Nat → Key
  deriving Inhabited, BEq, Repr
private nonrec def Key.hash : Key → UInt64
  | .star i     => mixHash 7883 <| hash i
  | .opaque     => 342
  | .const n a  => mixHash 5237 <| mixHash (hash n) (hash a)
  | .fvar  n a  => mixHash 8765 <| mixHash (hash n) (hash a)
  | .bvar i a   => mixHash 4323 <| mixHash (hash i) (hash a)
  | .lit v      => mixHash 1879 <| hash v
  | .sort       => 2411
  | .lam        => 4742
  | .«forall»   => 9752
  | .proj s i a => mixHash (hash a) <| mixHash (hash s) (hash i)
instance : Hashable Key := ⟨Key.hash⟩
def Key.ctorIdx : Key → Nat
  | .star ..   => 0
  | .opaque .. => 1
  | .const ..  => 2
  | .fvar ..   => 3
  | .bvar ..   => 4
  | .lit ..    => 5
  | .sort      => 6
  | .lam       => 7
  | .forall    => 8
  | .proj ..   => 9
private def Key.lt : Key → Key → Bool
  | .star i₁,       .star i₂       => i₁ < i₂
  | .const n₁ a₁,   .const n₂ a₂   => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | .fvar f₁ a₁,    .fvar f₂ a₂    => Name.quickLt f₁.name f₂.name || (f₁ == f₂ && a₁ < a₂)
  | .bvar i₁ a₁,    .bvar i₂ a₂    => i₁ < i₂ || (i₁ == i₂ && a₁ < a₂)
  | .lit v₁,        .lit v₂        => v₁ < v₂
  | .proj s₁ i₁ a₁, .proj s₂ i₂ a₂ => Name.quickLt s₁ s₂ ||
    (s₁ == s₂ && (i₁ < i₂ || (i₁ == i₂ && a₁ < a₂)))
  | k₁,             k₂             => k₁.ctorIdx < k₂.ctorIdx
instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))
private def Key.format : Key → Format
  | .star i                 => "*" ++ Std.format i
  | .opaque                 => "◾"
  | .const k a              => "⟨" ++ Std.format k ++ ", " ++ Std.format a ++ "⟩"
  | .fvar k a               => "⟨" ++ Std.format k.name ++ ", " ++ Std.format a ++ "⟩"
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .sort                   => "sort"
  | .bvar i a               => "⟨" ++ "#" ++ Std.format i ++ ", " ++ Std.format a ++ "⟩"
  | .lam                    => "λ"
  | .forall                 => "∀"
  | .proj s i a             => "⟨" ++ Std.format s ++"."++ Std.format i ++", "++ Std.format a ++ "⟩"
instance : ToFormat Key := ⟨Key.format⟩
def Key.arity : Key → Nat
  | .const _ a  => a
  | .fvar _ a   => a
  | .bvar _ a   => a
  | .lam        => 1
  | .forall     => 2
  | .proj _ _ a => 1 + a
  | _           => 0
variable {α : Type}
inductive Trie (α : Type) where
  | node (children : Array (Key × Trie α))
  | path (keys : Array Key) (child : Trie α)
  | values (vs : Array α)
instance : Inhabited (Trie α) := ⟨.node #[]⟩
def Trie.mkPath (keys : Array Key) (child : Trie α) :=
  if keys.isEmpty then child else Trie.path keys child
def Trie.singleton (keys : Array Key) (value : α) (i : Nat) : Trie α :=
  mkPath keys[i:] (values #[value])
def Trie.mkNode2 (k1 : Key) (t1 : Trie α) (k2 : Key) (t2 : Trie α) : Trie α :=
  if k1 < k2 then
    .node #[(k1, t1), (k2, t2)]
  else
    .node #[(k2, t2), (k1, t1)]
def Trie.values! : Trie α → Array α
  | .values vs => vs
  | _ => panic! "expected .values constructor"
def Trie.children! : Trie α → Array (Key × Trie α)
  | .node cs => cs
  | .path ks c => #[(ks[0]!, mkPath ks[1:] c)]
  | .values _ => panic! "did not expect .values constructor"
private partial def Trie.format [ToFormat α] : Trie α → Format
  | .node cs => Format.group <| Format.paren <|
    "node " ++ Format.join (cs.toList.map fun (k, c) =>
      Format.line ++ Format.paren (format (prepend k c)))
  | .values vs => if vs.isEmpty then Format.nil else Std.format vs
  | .path ks c => Format.sbracket (Format.joinSep ks.toList (", "))
      ++ " => " ++ Format.line ++ format c
where
  prepend (k : Key) (t : Trie α) : Trie α := match t with
    | .path ks c => .path (#[k] ++ ks) c
    | t => .path #[k] t
instance [ToFormat α] : ToFormat (Trie α) := ⟨Trie.format⟩
structure _root_.Mathlib.Meta.FunProp.RefinedDiscrTree (α : Type) where
  root : PersistentHashMap Key (Trie α) := {}
instance : Inhabited (RefinedDiscrTree α) := ⟨{}⟩
private partial def format [ToFormat α] (d : RefinedDiscrTree α) : Format :=
  let (_, r) := d.root.foldl
    (fun (p : Bool × Format) k c =>
      (false,
        p.2 ++ (if p.1 then Format.nil else Format.line) ++
          Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r
instance [ToFormat α] : ToFormat (RefinedDiscrTree α) := ⟨format⟩
inductive DTExpr where
  | star : Option MVarId → DTExpr
  | opaque : DTExpr
  | const : Name → Array DTExpr → DTExpr
  | fvar : FVarId → Array DTExpr → DTExpr
  | bvar : Nat → Array DTExpr → DTExpr
  | lit : Literal → DTExpr
  | sort : DTExpr
  | lam : DTExpr → DTExpr
  | forall : DTExpr → DTExpr → DTExpr
  | proj : Name → Nat → DTExpr → Array DTExpr → DTExpr
deriving Inhabited, BEq, Repr
private partial def DTExpr.format : DTExpr → Format
  | .star _                 => "*"
  | .opaque                 => "◾"
  | .const n as             => Std.format n ++ formatArgs as
  | .fvar n as              => Std.format n.name ++ formatArgs as
  | .bvar i as              => "#" ++ Std.format i  ++ formatArgs as
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .sort                   => "Sort"
  | .lam b                  => "λ " ++ DTExpr.format b
  | .forall d b             => DTExpr.format d ++ " → " ++ DTExpr.format b
  | .proj _ i a as          => DTExpr.format a ++ "." ++ Std.format i ++ formatArgs as
where
  formatArgs (as : Array DTExpr) :=
    if as.isEmpty
      then .nil
      else " " ++ Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")
instance : ToFormat DTExpr := ⟨DTExpr.format⟩
partial def DTExpr.size : DTExpr → Nat
| .const _ args
| .fvar _ args
| .bvar _ args => args.foldl (init := 1) (· + ·.size)
| .lam b => b.size
| .forall d b => 1 + d.size + b.size
| _ => 1
private def DTExpr.eqv (a b : DTExpr) : Bool :=
  (go a b).run' {}
where
  go (a b : DTExpr) : StateM (Std.HashMap MVarId MVarId) Bool :=
    match a, b with
    | .opaque           , .opaque            => pure true
    | .const n₁ as₁     , .const n₂ as₂      => pure (n₁ == n₂) <&&> goArray as₁ as₂
    | .fvar n₁ as₁      , .fvar n₂ as₂       => pure (n₁ == n₂) <&&> goArray as₁ as₂
    | .bvar i₁ as₁      , .bvar i₂ as₂       => pure (i₁ == i₂) <&&> goArray as₁ as₂
    | .lit li₁          , .lit li₂           => pure (li₁ == li₂)
    | .sort             , .sort              => pure true
    | .lam b₁           , .lam b₂            => go b₁ b₂
    | .forall d₁ b₁     , .forall d₂ b₂      => go d₁ d₂ <&&> go b₁ b₂
    | .proj n₁ i₁ a₁ as₁, .proj n₂ i₂ a₂ as₂ => pure (n₁ == n₂ && i₁ == i₂)
                                            <&&> go a₁ a₂ <&&> goArray as₁ as₂
    | .star none        , .star none         => pure true
    | .star (some id₁)  , .star (some id₂)   => modifyGet fun map => match map[id₁]? with
      | some id => (id == id₂, map)
      | none => (true, map.insert id₁ id₂)
    | _ , _ => return false
  goArray (as bs : Array DTExpr) : StateM (Std.HashMap MVarId MVarId) Bool := do
    if h : as.size = bs.size then
      for g : i in [:as.size] do
        unless ← go as[i] (bs[i]'(h ▸ g.2)) do
          return false
      return true
    else
      return false
private structure Flatten.State where
  stars : Array MVarId := #[]
private def getStar (mvarId? : Option MVarId) : StateM Flatten.State Nat :=
  modifyGet fun s =>
    match mvarId? with
    | some mvarId => match s.stars.findIdx? (· == mvarId) with
      | some idx => (idx, s)
      | none => (s.stars.size, { s with stars := s.stars.push mvarId })
    | none => (s.stars.size, { s with stars := s.stars.push ⟨.anonymous⟩ })
private partial def DTExpr.flattenAux (todo : Array Key) : DTExpr → StateM Flatten.State (Array Key)
  | .star i => return todo.push (.star (← getStar i))
  | .opaque => return todo.push .opaque
  | .const n as => as.foldlM flattenAux (todo.push (.const n as.size))
  | .fvar  f as => as.foldlM flattenAux (todo.push (.fvar f as.size))
  | .bvar  i as => as.foldlM flattenAux (todo.push (.bvar i as.size))
  | .lit l => return todo.push (.lit l)
  | .sort  => return todo.push .sort
  | .lam b => flattenAux (todo.push .lam) b
  | .«forall» d b => do flattenAux (← flattenAux (todo.push .forall) d) b
  | .proj n i e as => do as.foldlM flattenAux (← flattenAux (todo.push (.proj n i as.size)) e)
def DTExpr.flatten (e : DTExpr) (initCapacity := 16) : Array Key :=
  (DTExpr.flattenAux (.mkEmpty initCapacity) e).run' {}
private partial def isNumeral (e : Expr) : Bool :=
  if e.isRawNatLit then true
  else
    let f := e.getAppFn
    if !f.isConst then false
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then isNumeral e.appArg!
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then isNumeral (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then true
      else false
private partial def toNatLit? (e : Expr) : Option Literal :=
  if isNumeral e then
    if let some n := loop e then
      some (.natVal n)
    else
      none
  else
    none
where
  loop (e : Expr) : Option Nat := do
    let f := e.getAppFn
    match f with
    | .lit (.natVal n) => return n
    | .const fName .. =>
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then
        let r ← loop e.appArg!
        return r+1
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then
        loop (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then
        return 0
      else
        failure
    | _ => failure
partial def reduce (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  match (← unfoldDefinition? e) with
  | some e => reduce e
  | none => match e.etaExpandedStrict? with
    | some e => reduce e
    | none   => return e
@[specialize]
partial def lambdaTelescopeReduce {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    [Nonempty α] (e : Expr) (fvars : List FVarId)
    (k : Expr → List FVarId → m α) : m α := do
  match ← reduce e with
  | .lam n d b bi =>
    withLocalDecl n bi d fun fvar =>
      lambdaTelescopeReduce (b.instantiate1 fvar) (fvar.fvarId! :: fvars) k
  | e => k e fvars
def isStar : Expr → Bool
  | .mvar .. => true
  | .app f _ => isStar f
  | _ => false
def isStarWithArg (arg : Expr) : Expr → Bool
  | .app f a => if a == arg then isStar f else isStarWithArg arg f
  | _ => false
private partial def DTExpr.hasLooseBVarsAux (i : Nat) : DTExpr → Bool
  | .const  _ as   => as.any (hasLooseBVarsAux i)
  | .fvar   _ as   => as.any (hasLooseBVarsAux i)
  | .bvar j as     => j ≥ i || as.any (hasLooseBVarsAux i)
  | .proj _ _ a as => a.hasLooseBVarsAux i || as.any (hasLooseBVarsAux i)
  | .forall d b    => d.hasLooseBVarsAux i || b.hasLooseBVarsAux (i+1)
  | .lam b         => b.hasLooseBVarsAux (i+1)
  | _              => false
def DTExpr.hasLooseBVars (e : DTExpr) : Bool :=
  e.hasLooseBVarsAux 0
namespace MkDTExpr
private structure Context where
  bvars : List FVarId := []
  forbiddenVars : List FVarId := []
  fvarInContext : FVarId → Bool
def getIgnores (fn : Expr) (args : Array Expr) : MetaM (Array Bool) := do
  let mut fnType ← inferType fn
  let mut result := Array.mkEmpty args.size
  let mut j := 0
  for i in [:args.size] do
    unless fnType matches .forallE .. do
      fnType ← whnfD (fnType.instantiateRevRange j i args)
      j := i
    let .forallE _ d b bi := fnType | throwError m! "expected function type {indentExpr fnType}"
    fnType := b
    result := result.push (← isIgnoredArg args[i]! d bi)
  return result
where
  isIgnoredArg (arg domain : Expr) (binderInfo : BinderInfo) : MetaM Bool := do
    if domain.isOutParam then
      return true
    match binderInfo with
    | .instImplicit => return true
    | .implicit
    | .strictImplicit => return !(← isType arg)
    | .default => isProof arg
@[specialize]
def etaExpand (args : Array Expr) (type : Expr) (lambdas : List FVarId) (goalArity : Nat)
    (k : Array Expr → List FVarId → MetaM α) : MetaM α  := do
  if args.size < goalArity then
    withLocalDeclD `_η type fun fvar =>
      etaExpand (args.push fvar) type (fvar.fvarId! :: lambdas) goalArity k
  else
    k args lambdas
def reduceHBinOpAux (args : Array Expr) (lambdas : List FVarId) (instH instPi : Name) :
    OptionT MetaM (Expr × Expr × Expr × List FVarId) := do
  let some (mkApp2 (.const instH' _) type inst) := args[3]? | failure
  guard (instH == instH')
  if args.size ≤ 6 then
    etaExpand args type lambdas 6 fun args lambdas =>
      distributeLambdas lambdas type args[4]! args[5]!
  else
  let mut type := type
  let mut inst := inst
  let mut lhs := args[4]!
  let mut rhs := args[5]!
  for arg in args[6:] do
    let mkApp3 (.const i _) _ f inst' := inst | return (type, lhs, rhs, lambdas)
    unless i == instPi do return (type, lhs, rhs, lambdas)
    type := .app f arg
    inst := inst'
    lhs := .app lhs arg
    rhs := .app rhs arg
  distributeLambdas lambdas type lhs rhs
where
  distributeLambdas (lambdas : List FVarId) (type lhs rhs : Expr) :
    MetaM (Expr × Expr × Expr × List FVarId) := match lambdas with
    | fvarId :: lambdas => do
      let decl ← fvarId.getDecl
      let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
      let lhs  := .lam     decl.userName decl.type (lhs.abstract  #[.fvar fvarId]) decl.binderInfo
      let rhs  := .lam     decl.userName decl.type (rhs.abstract  #[.fvar fvarId]) decl.binderInfo
      distributeLambdas lambdas type lhs rhs
    | [] => return (type, lhs, rhs, [])
@[inline] def reduceHBinOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Expr × Expr × Expr × List FVarId)) :=
  match n with
  | ``HAdd.hAdd => reduceHBinOpAux args lambdas ``instHAdd ``Pi.instAdd
  | ``HMul.hMul => reduceHBinOpAux args lambdas ``instHMul ``Pi.instMul
  | ``HSub.hSub => reduceHBinOpAux args lambdas ``instHSub ``Pi.instSub
  | ``HDiv.hDiv => reduceHBinOpAux args lambdas ``instHDiv ``Pi.instDiv
  | _ => return none
def reduceUnOpAux (args : Array Expr) (lambdas : List FVarId) (instPi : Name) :
    OptionT MetaM (Expr × Expr × List FVarId) := do
  guard (args.size ≥ 3)
  let mut type := args[0]!
  let mut inst := args[1]!
  let mut arg := args[2]!
  if args.size == 3 then
    distributeLambdas lambdas type arg
  else
  for arg' in args[3:] do
    let mkApp3 (.const i _) _ f inst' := inst | return (type, arg, lambdas)
    unless i == instPi do return (type, arg, lambdas)
    type := .app f arg'
    inst := inst'
    arg := .app arg arg'
  distributeLambdas lambdas type arg
where
  distributeLambdas (lambdas : List FVarId) (type arg : Expr) :
    MetaM (Expr × Expr × List FVarId) := match lambdas with
    | fvarId :: lambdas => do
      let decl ← fvarId.getDecl
      let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
      let arg  := .lam     decl.userName decl.type (arg.abstract  #[.fvar fvarId]) decl.binderInfo
      distributeLambdas lambdas type arg
    | [] => return (type, arg, [])
@[inline] def reduceUnOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Expr × Expr × List FVarId)) :=
  match n with
  | ``Neg.neg => reduceUnOpAux args lambdas ``Pi.instNeg
  | ``Inv.inv => reduceUnOpAux args lambdas ``Pi.instInv
  | _ => return none
@[specialize]
private def withLams {m} [Monad m] [MonadWithReader Context m]
    (lambdas : List FVarId) (k : m DTExpr) : m DTExpr :=
  if lambdas.isEmpty then
    k
  else do
    let e ← withReader (fun c => { c with bvars := lambdas ++ c.bvars }) k
    return lambdas.foldl (fun _ => ·.lam) e
partial def mkDTExprAux (e : Expr) (root : Bool) : ReaderT Context MetaM DTExpr := do
  lambdaTelescopeReduce e [] fun e lambdas =>
  e.withApp fun fn args => do
  let argDTExpr (arg : Expr) (ignore : Bool) : ReaderT Context MetaM DTExpr :=
    if ignore then pure (.star none) else mkDTExprAux arg false
  let argDTExprs : ReaderT Context MetaM (Array DTExpr) := do
    let ignores ← getIgnores fn args
    args.mapIdxM fun i arg =>
      argDTExpr arg ignores[i]!
  match fn with
  | .const n _ =>
    unless root do
      if let some (type, lhs, rhs, lambdas') ← reduceHBinOp n args lambdas then
        return ← withLams lambdas' do
          let type ← mkDTExprAux type false
          let lhs ← mkDTExprAux lhs false
          let rhs ← mkDTExprAux rhs false
          return .const n #[type, type, .star none, .star none, lhs, rhs]
      if let some (type, arg, lambdas') ← reduceUnOp n e.getAppArgs lambdas then
        return ← withLams lambdas' do
          let type ← mkDTExprAux type false
          let arg ← mkDTExprAux arg false
          return .const n #[type, .star none, arg]
      if let some v := toNatLit? e then
        return .lit v
    withLams lambdas do
      return .const n (← argDTExprs)
  | .proj s i a =>
    withLams lambdas do
      let a ← argDTExpr a (isClass (← getEnv) s)
      return .proj s i a (← argDTExprs)
  | .fvar fvarId =>
    if let fvarId' :: lambdas' := lambdas then
      if fvarId' == fvarId && args.isEmpty && !root then
        return ← withLams lambdas' do
          let type ← mkDTExprAux (← fvarId.getType) false
          return .const ``id #[type]
    withLams lambdas do
      if let some idx := (← read).bvars.findIdx? (· == fvarId) then
        return .bvar idx (← argDTExprs)
      if (← read).fvarInContext fvarId then
        return .fvar fvarId (← argDTExprs)
      else
        return .opaque
  | .mvar mvarId =>
    if args.isEmpty then
      withLams lambdas do return .star (some mvarId)
    else
      return .star none
  | .forallE n d b bi =>
    withLams lambdas do
      let d' ← mkDTExprAux d false
      let b' ← withLocalDecl n bi d fun fvar =>
        withReader (fun c => { c with bvars := fvar.fvarId! :: c.bvars }) do
          mkDTExprAux (b.instantiate1 fvar) false
      return .forall d' b'
  | .lit v      => withLams lambdas do return .lit v
  | .sort _     => withLams lambdas do return .sort
  | .letE ..    => withLams lambdas do return .opaque
  | .lam ..     => withLams lambdas do return .opaque
  | _           => unreachable!
private abbrev M := StateListT (AssocList Expr DTExpr) <| ReaderT Context MetaM
instance : MonadCache Expr DTExpr M where
  findCached? e := do
    let s ← get
    return s.find? e
  cache e e' :=
    if e'.hasLooseBVars then
      return
    else
      modify (·.insert e e')
@[specialize]
def etaPossibilities (e : Expr) (lambdas : List FVarId) (k : Expr → List FVarId → M α) : M α :=
  k e lambdas
  <|> do
  match e, lambdas with
  | .app f a, fvarId :: lambdas =>
    if isStarWithArg (.fvar fvarId) a then
      withReader (fun c => { c with forbiddenVars := fvarId :: c.forbiddenVars }) do
        etaPossibilities f lambdas k
    else
      failure
  | _, _ => failure
@[specialize]
def cacheEtaPossibilities (e original : Expr) (lambdas : List FVarId)
    (k : Expr → List FVarId → M DTExpr) : M DTExpr :=
  match e, lambdas with
  | .app _ a, fvarId :: _ =>
    if isStarWithArg (.fvar fvarId) a then
      checkCache original fun _ =>
        etaPossibilities e lambdas k
    else
      k e lambdas
  | _, _ => k e lambdas
partial def mkDTExprsAux (original : Expr) (root : Bool) : M DTExpr := do
  lambdaTelescopeReduce original [] fun e lambdas => do
  if !root then
    if let .const n _ := e.getAppFn then
      if let some (type, lhs, rhs, lambdas') ← reduceHBinOp n e.getAppArgs lambdas then
        return ← withLams lambdas' do
          let type ← mkDTExprsAux type false
          let lhs ← mkDTExprsAux lhs false
          let rhs ← mkDTExprsAux rhs false
          return .const n #[type, type, .star none, .star none, lhs, rhs]
      if let some (type, arg, lambdas') ← reduceUnOp n e.getAppArgs lambdas then
        return ← withLams lambdas' do
          let type ← mkDTExprsAux type false
          let arg ← mkDTExprsAux arg false
          return .const n #[type, .star none, arg]
  cacheEtaPossibilities e original lambdas fun e lambdas =>
  e.withApp fun fn args => do
  let argDTExpr (arg : Expr) (ignore : Bool) : M DTExpr :=
    if ignore then pure (.star none) else mkDTExprsAux arg false
  let argDTExprs : M (Array DTExpr) := do
    let ignores ← getIgnores fn args
    args.mapIdxM fun i arg =>
      argDTExpr arg ignores[i]!
  match fn with
  | .const n _ =>
      unless root do
        if let some v := toNatLit? e then
          return .lit v
      withLams lambdas do
        return .const n (← argDTExprs)
  | .proj s i a =>
    withLams lambdas do
    let a ← argDTExpr a (isClass (← getEnv) s)
    return .proj s i a (← argDTExprs)
  | .fvar fvarId =>
    if let fvarId' :: lambdas' := lambdas then
      if fvarId' == fvarId && args.isEmpty && !root then
        return ← withLams lambdas' do
          let type ← mkDTExprAux (← fvarId.getType) false
          return .const ``id #[type]
    withLams lambdas do
      let c ← read
      if let some idx := c.bvars.findIdx? (· == fvarId) then
        return .bvar idx (← argDTExprs)
      guard !(c.forbiddenVars.contains fvarId)
      if c.fvarInContext fvarId then
        return .fvar fvarId (← argDTExprs)
      else
        return .opaque
  | .mvar mvarId =>
    if args.isEmpty then
      withLams lambdas do return .star (some mvarId)
    else
      return .star none
  | .forallE n d b bi =>
    withLams lambdas do
    let d' ← mkDTExprsAux d false
    let b' ← withLocalDecl n bi d fun fvar =>
      withReader (fun c => { c with bvars := fvar.fvarId! :: c.bvars }) do
        mkDTExprsAux (b.instantiate1 fvar) false
    return .forall d' b'
  | .lit v      => withLams lambdas do return .lit v
  | .sort _     => withLams lambdas do return .sort
  | .letE ..    => withLams lambdas do return .opaque
  | .lam ..     => withLams lambdas do return .opaque
  | _           => unreachable!
end MkDTExpr
def DTExpr.isSpecific : DTExpr → Bool
  | .star _
  | .const ``Eq #[.star _, .star _, .star _] => false
  | _ => true
def mkDTExpr (e : Expr)
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM DTExpr :=
  withReducible do (MkDTExpr.mkDTExprAux e true |>.run {fvarInContext})
def mkDTExprs (e : Expr) (onlySpecific : Bool)
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM (List DTExpr) :=
  withReducible do
    let es ← (MkDTExpr.mkDTExprsAux e true).run' {} |>.run {fvarInContext}
    return if onlySpecific then es.filter (·.isSpecific) else es
private def insertInArray [BEq α] (vs : Array α) (v : α) : Array α :=
  loop 0
where
  loop (i : Nat) : Array α :=
    if h : i < vs.size then
      if v == vs[i] then
        vs.set i v
      else
        loop (i+1)
    else
      vs.push v
partial def insertInTrie [BEq α] (keys : Array Key) (v : α) (i : Nat) : Trie α → Trie α
  | .node cs =>
      let k := keys[i]!
      let c := Id.run <| cs.binInsertM
        (fun a b => a.1 < b.1)
        (fun (k', s) => (k', insertInTrie keys v (i+1) s))
        (fun _ => (k, Trie.singleton keys v (i+1)))
        (k, default)
      .node c
  | .values vs =>
      .values (insertInArray vs v)
  | .path ks c => Id.run do
    for n in [:ks.size] do
      let k1 := keys[i+n]!
      let k2 := ks[n]!
      if k1 != k2 then
        let shared := ks[:n]
        let rest := ks[n+1:]
        return .mkPath shared (.mkNode2 k1 (.singleton keys v (i+n+1)) k2 (.mkPath rest c))
    return .path ks (insertInTrie keys v (i + ks.size) c)
def insertInRefinedDiscrTree [BEq α] (d : RefinedDiscrTree α) (keys : Array Key) (v : α) :
    RefinedDiscrTree α :=
  let k := keys[0]!
  match d.root.find? k with
  | none =>
    let c := .singleton keys v 1
    { root := d.root.insert k c }
  | some c =>
    let c := insertInTrie keys v 1 c
    { root := d.root.insert k c }
def insertDTExpr [BEq α] (d : RefinedDiscrTree α) (e : DTExpr) (v : α) : RefinedDiscrTree α :=
  insertInRefinedDiscrTree d e.flatten v
def insert [BEq α] (d : RefinedDiscrTree α) (e : Expr) (v : α)
    (onlySpecific : Bool := true) (fvarInContext : FVarId → Bool := fun _ => false) :
    MetaM (RefinedDiscrTree α) := do
  let keys ← mkDTExprs e onlySpecific fvarInContext
  return keys.foldl (insertDTExpr · · v) d
def insertEqn [BEq α] (d : RefinedDiscrTree α) (lhs rhs : Expr) (vLhs vRhs : α)
    (onlySpecific : Bool := true) (fvarInContext : FVarId → Bool := fun _ => false) :
    MetaM (RefinedDiscrTree α) := do
  let keysLhs ← mkDTExprs lhs onlySpecific fvarInContext
  let keysRhs ← mkDTExprs rhs onlySpecific fvarInContext
  let d := keysLhs.foldl (insertDTExpr · · vLhs) d
  if @List.beq _ ⟨DTExpr.eqv⟩ keysLhs keysRhs then
    return d
  else
    return keysRhs.foldl (insertDTExpr · · vRhs) d
namespace GetUnify
def findKey (children : Array (Key × Trie α)) (k : Key) : Option (Trie α) :=
  (·.2) <$> children.binSearch (k, default) (fun a b => a.1 < b.1)
private structure Context where
  unify : Bool
private structure State where
  score : Nat := 0
  starAssignments : Std.HashMap Nat DTExpr := {}
  mvarAssignments : Std.HashMap MVarId (Array Key) := {}
private abbrev M := ReaderT Context <| StateListM State
private def M.run (unify : Bool) (x : M (Trie α)) :
    Array (Array α × Nat) :=
  ((x.run { unify }).run {}).toArray.map (fun (t, s) => (t.values!, s.score))
private def incrementScore (n : Nat) : M Unit :=
  modify fun s => { s with score := s.score + n }
private def insertStarAssignment (n : Nat) (e : DTExpr) : M Unit :=
  modify fun s => { s with starAssignments := s.starAssignments.insert n e }
private def assignMVar (mvarId : MVarId) (e : Array Key) : M Unit := do
  let { mvarAssignments, .. } ← get
  match mvarAssignments[mvarId]? with
  | some e' => guard (e == e')
  | none =>
    modify fun s => { s with mvarAssignments := s.mvarAssignments.insert mvarId e }
partial def skipEntries (t : Trie α) (skipped : Array Key) : Nat → M (Array Key × Trie α)
  | 0      => pure (skipped, t)
  | skip+1 =>
    t.children!.foldr (init := failure) fun (k, c) x =>
      (skipEntries c (skipped.push k) (skip + k.arity)) <|> x
def matchTargetStar (mvarId? : Option MVarId) (t : Trie α) : M (Trie α) := do
  let (keys, t) ← t.children!.foldr (init := failure) fun (k, c) x => (do
    if k == .opaque then
      incrementScore 1
    skipEntries c #[k] k.arity
    ) <|> x
  if let some mvarId := mvarId? then
    assignMVar mvarId keys
  return t
def matchTreeStars (e : DTExpr) (t : Trie α) : M (Trie α) := do
  let {starAssignments, ..} ← get
  let mut result := failure
  for (k, c) in t.children! do
    let .star i := k | break
    if let some assignment := starAssignments[i]? then
      if e == assignment then
        result := (incrementScore e.size *> pure c) <|> result
    else
      result := (insertStarAssignment i e *> pure c) <|> result
  result
mutual
  partial def matchExpr (e : DTExpr) (t : Trie α) : M (Trie α) := do
    if let .star mvarId? := e then
      if (← read).unify then
        matchTargetStar mvarId? t
      else
        matchTreeStars e t
    else
      matchTreeStars e t <|> exactMatch e (findKey t.children!)
  @[specialize]
  partial def exactMatch (e : DTExpr) (find? : Key → Option (Trie α)) : M (Trie α) := do
    let findKey (k : Key) (x : Trie α → M (Trie α) := pure) (score := 1) : M (Trie α) :=
      match find? k with
        | none => failure
        | some trie => do
          incrementScore score
          x trie
    let matchArgs (args : Array DTExpr) : Trie α → M (Trie α) :=
      args.foldlM (fun t e => matchExpr e t)
    match e with
    | .opaque           => failure
    | .const c args     => findKey (.const c args.size) (matchArgs args)
    | .fvar fvarId args => findKey (.fvar fvarId args.size) (matchArgs args)
    | .bvar i args      => findKey (.bvar i args.size) (matchArgs args)
    | .lit v            => findKey (.lit v)
    | .sort             => findKey .sort
    | .lam b            => findKey .lam (matchExpr b) 0
    | .forall d b       => findKey .forall (matchExpr d >=> matchExpr b)
    | .proj n i a args  => findKey (.proj n i args.size) (matchExpr a >=> matchArgs args)
    | _                 => unreachable!
end
private partial def getMatchWithScoreAux (d : RefinedDiscrTree α) (e : DTExpr) (unify : Bool)
    (allowRootStar : Bool := false) : Array (Array α × Nat) := (do
  if e matches .star _ then
    guard allowRootStar
    d.root.foldl (init := failure) fun x k c => (do
      if k == Key.opaque then
        GetUnify.incrementScore 1
      let (_, t) ← GetUnify.skipEntries c #[k] k.arity
      return t) <|> x
  else
    GetUnify.exactMatch e d.root.find?
    <|> do
    guard allowRootStar
    let some c := d.root.find? (.star 0) | failure
    return c
  ).run unify
end GetUnify
def getMatchWithScore (d : RefinedDiscrTree α) (e : Expr) (unify : Bool)
    (allowRootStar : Bool := false) : MetaM (Array (Array α × Nat)) := do
  let e ← mkDTExpr e
  let result := GetUnify.getMatchWithScoreAux d e unify allowRootStar
  return result.qsort (·.2 > ·.2)
partial def getMatchWithScoreWithExtra (d : RefinedDiscrTree α) (e : Expr) (unify : Bool)
    (allowRootStar : Bool := false) :
    MetaM (Array (Array α × Nat × Nat)) := do
  let result ← go e 0
  return result.qsort (·.2.1 > ·.2.1)
where
  go (e : Expr) (numIgnored : Nat) : MetaM (Array (Array α × Nat × Nat)) := do
  let result ← getMatchWithScore d e unify allowRootStar
  let result := result.map fun (a, b) => (a, b, numIgnored)
  match e with
  | .app e _ => return (← go e (numIgnored + 1)) ++ result
  | _ => return result
variable {β : Type} {m : Type → Type} [Monad m]
partial def Trie.mapArraysM (t : RefinedDiscrTree.Trie α) (f : Array α → m (Array β)) :
    m (Trie β) := do
  match t with
  | .node children =>
    return .node (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))
  | .values vs =>
    return .values (← f vs)
  | .path ks c =>
    return .path ks (← c.mapArraysM f)
def mapArraysM (d : RefinedDiscrTree α) (f : Array α → m (Array β)) : m (RefinedDiscrTree β) :=
  return { root := ← d.root.mapM (·.mapArraysM f) }
def mapArrays (d : RefinedDiscrTree α) (f : Array α → Array β) : RefinedDiscrTree β :=
  d.mapArraysM (m := Id) f
end Mathlib.Meta.FunProp.RefinedDiscrTree