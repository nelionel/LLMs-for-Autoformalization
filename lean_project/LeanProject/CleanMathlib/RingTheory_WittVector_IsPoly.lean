import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Ring.ULift
import Mathlib.RingTheory.WittVector.Basic
namespace WittVector
universe u
variable {p : ℕ} {R S : Type u} {idx : Type*} [CommRing R] [CommRing S]
local notation "𝕎" => WittVector p 
open MvPolynomial
open Function (uncurry)
variable (p)
noncomputable section
theorem poly_eq_of_wittPolynomial_bind_eq' [Fact p.Prime] (f g : ℕ → MvPolynomial (idx × ℕ) ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [Function.comp_def, map_bind₁, map_wittPolynomial, ← bind₁_bind₁,
    bind₁_wittPolynomial_xInTermsOfW, bind₁_X_right] using h
theorem poly_eq_of_wittPolynomial_bind_eq [Fact p.Prime] (f g : ℕ → MvPolynomial ℕ ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [Function.comp_def, map_bind₁, map_wittPolynomial, ← bind₁_bind₁,
    bind₁_wittPolynomial_xInTermsOfW, bind₁_X_right] using h
class IsPoly (f : ∀ ⦃R⦄ [CommRing R], WittVector p R → 𝕎 R) : Prop where mk' ::
  poly :
    ∃ φ : ℕ → MvPolynomial ℕ ℤ,
      ∀ ⦃R⦄ [CommRing R] (x : 𝕎 R), (f x).coeff = fun n => aeval x.coeff (φ n)
instance idIsPoly : IsPoly p fun _ _ => id :=
  ⟨⟨X, by intros; simp only [aeval_X, id]⟩⟩
instance idIsPolyI' : IsPoly p fun _ _ a => a :=
  WittVector.idIsPoly _
namespace IsPoly
instance : Inhabited (IsPoly p fun _ _ => id) :=
  ⟨WittVector.idIsPoly p⟩
variable {p}
theorem ext [Fact p.Prime] {f g} (hf : IsPoly p f) (hg : IsPoly p g)
    (h : ∀ (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R) (n : ℕ),
        ghostComponent n (f x) = ghostComponent n (g x)) :
    ∀ (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R), f x = g x := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf, hg, poly_eq_of_wittPolynomial_bind_eq p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift ℤ) (mk p fun i => ⟨x i⟩) k
  simp only [ghostComponent_apply, aeval_eq_eval₂Hom] at h
  apply (ULift.ringEquiv.symm : ℤ ≃+* _).injective
  simp only [← RingEquiv.coe_toRingHom, map_eval₂Hom]
  convert h using 1
  all_goals
    simp only [hf, hg, MvPolynomial.eval, map_eval₂Hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    simp only [coeff_mk]; rfl
instance comp {g f} [hg : IsPoly p g] [hf : IsPoly p f] :
    IsPoly p fun R _Rcr => @g R _Rcr ∘ @f R _Rcr := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [aeval_bind₁, Function.comp, hg, hf]
end IsPoly
class IsPoly₂ (f : ∀ ⦃R⦄ [CommRing R], WittVector p R → 𝕎 R → 𝕎 R) : Prop where mk' ::
  poly :
    ∃ φ : ℕ → MvPolynomial (Fin 2 × ℕ) ℤ,
      ∀ ⦃R⦄ [CommRing R] (x y : 𝕎 R), (f x y).coeff = fun n => peval (φ n) ![x.coeff, y.coeff]
variable {p}
instance IsPoly₂.comp {h f g} [hh : IsPoly₂ p h] [hf : IsPoly p f] [hg : IsPoly p g] :
    IsPoly₂ p fun _ _Rcr x y => h (f x) (g y) := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  obtain ⟨χ, hh⟩ := hh
  refine ⟨⟨fun n ↦ bind₁ (uncurry <|
    ![fun k ↦ rename (Prod.mk (0 : Fin 2)) (φ k),
      fun k ↦ rename (Prod.mk (1 : Fin 2)) (ψ k)]) (χ n), ?_⟩⟩
  intros
  funext n
  simp (config := { unfoldPartialApp := true }) only [peval, aeval_bind₁, Function.comp, hh, hf, hg,
    uncurry]
  apply eval₂Hom_congr rfl _ rfl
  ext ⟨i, n⟩
  fin_cases i <;> simp [aeval_eq_eval₂Hom, eval₂Hom_rename, Function.comp_def]
instance IsPoly.comp₂ {g f} [hg : IsPoly p g] [hf : IsPoly₂ p f] :
    IsPoly₂ p fun _ _Rcr x y => g (f x y) := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [peval, aeval_bind₁, Function.comp, hg, hf]
instance IsPoly₂.diag {f} [hf : IsPoly₂ p f] : IsPoly p fun _ _Rcr x => f x x := by
  obtain ⟨φ, hf⟩ := hf
  refine ⟨⟨fun n => bind₁ (uncurry ![X, X]) (φ n), ?_⟩⟩
  intros; funext n
  simp (config := { unfoldPartialApp := true }) only [hf, peval, uncurry, aeval_bind₁]
  apply eval₂Hom_congr rfl _ rfl
  ext ⟨i, k⟩
  fin_cases i <;> simp
instance negIsPoly [Fact p.Prime] : IsPoly p fun R _ => @Neg.neg (𝕎 R) _ :=
  ⟨⟨fun n => rename Prod.snd (wittNeg p n), by
      intros; funext n
      rw [neg_coeff, aeval_eq_eval₂Hom, eval₂Hom_rename]
      apply eval₂Hom_congr rfl _ rfl
      ext ⟨i, k⟩; fin_cases i; rfl⟩⟩
section ZeroOne
instance zeroIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 0 :=
  ⟨⟨0, by intros; funext n; simp only [Pi.zero_apply, map_zero, zero_coeff]⟩⟩
@[simp]
theorem bind₁_zero_wittPolynomial [Fact p.Prime] (n : ℕ) :
    bind₁ (0 : ℕ → MvPolynomial ℕ R) (wittPolynomial p R n) = 0 := by
  rw [← aeval_eq_bind₁, aeval_zero, constantCoeff_wittPolynomial, RingHom.map_zero]
def onePoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if n = 0 then 1 else 0
@[simp]
theorem bind₁_onePoly_wittPolynomial [hp : Fact p.Prime] (n : ℕ) :
    bind₁ onePoly (wittPolynomial p ℤ n) = 1 := by
  rw [wittPolynomial_eq_sum_C_mul_X_pow, map_sum, Finset.sum_eq_single 0]
  · simp only [onePoly, one_pow, one_mul, map_pow, C_1, pow_zero, bind₁_X_right, if_true,
      eq_self_iff_true]
  · intro i _hi hi0
    simp only [onePoly, if_neg hi0, zero_pow (pow_ne_zero _ hp.1.ne_zero), mul_zero, map_pow,
      bind₁_X_right, map_mul]
  · simp
instance oneIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 1 :=
  ⟨⟨onePoly, by
      intros; funext n; cases n
      · simp only [lt_self_iff_false, one_coeff_zero, onePoly, ite_true, map_one]
      · simp only [Nat.succ_pos', one_coeff_eq_of_pos, onePoly, Nat.succ_ne_zero, ite_false,
          map_zero]
  ⟩⟩
end ZeroOne
instance addIsPoly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· + ·) :=
  ⟨⟨wittAdd p, by intros; ext; exact add_coeff _ _ _⟩⟩
instance mulIsPoly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· * ·) :=
  ⟨⟨wittMul p, by intros; ext; exact mul_coeff _ _ _⟩⟩
theorem IsPoly.map [Fact p.Prime] {f} (hf : IsPoly p f) (g : R →+* S) (x : 𝕎 R) :
    map g (f x) = f (map g x) := by
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp only [map_coeff, hf, map_aeval]
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  ext  
  simp only [map_coeff]
namespace IsPoly₂
instance [Fact p.Prime] : Inhabited (IsPoly₂ p (fun _ _ => (· + ·))) :=
  ⟨addIsPoly₂⟩
theorem compLeft {g f} [IsPoly₂ p g] [IsPoly p f] :
    IsPoly₂ p fun _R _Rcr x y => g (f x) y :=
  inferInstance
theorem compRight {g f} [IsPoly₂ p g] [IsPoly p f] :
    IsPoly₂ p fun _R _Rcr x y => g x (f y) :=
  inferInstance
theorem ext [Fact p.Prime] {f g} (hf : IsPoly₂ p f) (hg : IsPoly₂ p g)
    (h : ∀ (R : Type u) [_Rcr : CommRing R] (x y : 𝕎 R) (n : ℕ),
        ghostComponent n (f x y) = ghostComponent n (g x y)) :
    ∀ (R) [_Rcr : CommRing R] (x y : 𝕎 R), f x y = g x y := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf, hg, poly_eq_of_wittPolynomial_bind_eq' p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift ℤ) (mk p fun i => ⟨x (0, i)⟩) (mk p fun i => ⟨x (1, i)⟩) k
  simp only [ghostComponent_apply, aeval_eq_eval₂Hom] at h
  apply (ULift.ringEquiv.symm : ℤ ≃+* _).injective
  simp only [← RingEquiv.coe_toRingHom, map_eval₂Hom]
  convert h using 1
  all_goals
    simp only [hf, hg, MvPolynomial.eval, map_eval₂Hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext ⟨b, _⟩
    fin_cases b <;> simp only [coeff_mk, uncurry] <;> rfl
theorem map [Fact p.Prime] {f} (hf : IsPoly₂ p f) (g : R →+* S) (x y : 𝕎 R) :
    map g (f x y) = f (map g x) (map g y) := by
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp (config := { unfoldPartialApp := true }) only [map_coeff, hf, map_aeval, peval, uncurry]
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  ext ⟨i, k⟩
  fin_cases i <;> simp
end IsPoly₂
attribute [ghost_simps] AlgHom.id_apply map_natCast RingHom.map_zero RingHom.map_one RingHom.map_mul
  RingHom.map_add RingHom.map_sub RingHom.map_neg RingHom.id_apply mul_add add_mul add_zero zero_add
  mul_one one_mul mul_zero zero_mul Nat.succ_ne_zero add_tsub_cancel_right
  Nat.succ_eq_add_one if_true eq_self_iff_true if_false forall_true_iff forall₂_true_iff
  forall₃_true_iff
end
namespace Tactic
open Lean Parser.Tactic Elab.Tactic
syntax (name := ghostSimp) "ghost_simp" (simpArgs)? : tactic
macro_rules
  | `(tactic| ghost_simp $[[$simpArgs,*]]?) => do
    let args := simpArgs.map (·.getElems) |>.getD #[]
    `(tactic| simp only [← sub_eq_add_neg, ghost_simps, $args,*])
syntax (name := ghostCalc) "ghost_calc" (ppSpace colGt term:max)* : tactic
private def runIntro (ref : Syntax) (n : Name) : TacticM FVarId := do
  let fvarId ← liftMetaTacticAux fun g => do
    let (fv, g') ← g.intro n
    return (fv, [g'])
  withMainContext do
    Elab.Term.addLocalVarInfo ref (mkFVar fvarId)
  return fvarId
private def getLocalOrIntro (t : Term) : TacticM FVarId := do
  match t with
    | `(_) => runIntro t `_
    | `($id:ident) => getFVarId id <|> runIntro id id.getId
    | _ => Elab.throwUnsupportedSyntax
elab_rules : tactic | `(tactic| ghost_calc $[$ids']*) => do
  let ids ← ids'.mapM getLocalOrIntro
  withMainContext do
  let idsS ← ids.mapM (fun id => Elab.Term.exprToSyntax (.fvar id))
  let some (α, lhs, rhs) := (← getMainTarget'').eq?
    | throwError "ghost_calc expecting target to be an equality"
  let (``WittVector, #[_, R]) := α.getAppFnArgs
    | throwError "ghost_calc expecting target to be an equality of `WittVector`s"
  let instR ← Meta.synthInstance (← Meta.mkAppM ``CommRing #[R])
  unless instR.isFVar do
    throwError "{← Meta.inferType instR} instance is not local"
  let f ← Meta.mkLambdaFVars (#[R, instR] ++ ids.map .fvar) lhs
  let g ← Meta.mkLambdaFVars (#[R, instR] ++ ids.map .fvar) rhs
  let fS ← Elab.Term.exprToSyntax f
  let gS ← Elab.Term.exprToSyntax g
  match idsS with
    | #[x] => evalTactic (← `(tactic| refine IsPoly.ext (f := $fS) (g := $gS) ?_ ?_ ?_ _ $x))
    | #[x, y] => evalTactic (← `(tactic| refine IsPoly₂.ext (f := $fS) (g := $gS) ?_ ?_ ?_ _ $x $y))
    | _ => throwError "ghost_calc takes either one or two arguments"
  let nm ← withMainContext <|
    if let .fvar fvarId := (R : Expr) then
      fvarId.getUserName
    else
      Meta.getUnusedUserName `R
  evalTactic <| ← `(tactic| iterate 2 infer_instance)
  let R := mkIdent nm
  evalTactic <| ← `(tactic| clear! $R)
  evalTactic <| ← `(tactic| intro $(mkIdent nm):ident $(mkIdent (.str nm "_inst")):ident $ids'*)
end Tactic
end WittVector