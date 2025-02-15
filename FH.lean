set_option pp.fieldNotation false

-- Variables, Values and States -------------------------------

abbrev Val := Nat
abbrev Vname := String

abbrev State := Vname -> Val
-- update state
def upd (s: State) (x: Vname) (v: Val) : State :=
  λ y => if y = x then v else s y

notation:10 s " [ " x " := " v " ] " => upd s x v

-- Arithmetic Expressions -------------------------------------

inductive Aexp where
  | num : Val -> Aexp
  | var : Vname -> Aexp
  | add : Aexp -> Aexp -> Aexp
  | sub : Aexp -> Aexp -> Aexp
  deriving Repr

open Aexp

class ToAexp (a : Type) where
  toAexp : a -> Aexp

@[simp]
instance : ToAexp Nat where
  toAexp := num

@[simp]
instance : ToAexp String where
  toAexp := var

@[simp]
instance : ToAexp Aexp where
  toAexp a := a

@[simp]
instance : OfNat Aexp (n: Nat) where
  ofNat := num n

@[simp]
instance : Add Aexp where
  add := fun a1 a2 => add a1 a2

@[simp]
instance : HAdd String Aexp Aexp where
   hAdd := fun s a => add (var s) a

@[simp]
instance : HAdd String Nat Aexp where
   hAdd := fun s a => add (var s) (num a)

@[simp]
instance : HAdd String String Aexp where
   hAdd := fun s a => add (var s) (var a)

@[simp]
instance : HSub String Nat Aexp where
   hSub := fun s a => sub (var s) (num a)


def mkVar (s: String) (i : Nat) : Aexp := var (s!"{s}_{i}")

notation:80 lhs:91 "#" rhs:90 => mkVar lhs rhs

@[simp]
def x := "x"

@[simp]
def y := "y"

@[simp]
def z := "z"

def aexp0 : Aexp := x#1 + y#1 + z#1 + 5

def aval (a: Aexp) (s: State) : Val :=
  match a with
  | num n => n
  | var x => s x
  | add a1 a2 => aval a1 s + aval a2 s
  | sub a1 a2 => aval a1 s - aval a2 s

-- initial state
def st0 : State := λ _ => 0
def aexp_5 := num 5
def aexp_x := var "x"
def aexp_x_plus_y := add (var "x") (var "y")
def aexp_2_plus_z_plus_3 := add (num 2) (add (var "z") (num 3))

-- Substitution -----------------------------------------------

def subst (x : Vname) (xa : Aexp) (a : Aexp) : Aexp :=
  match a with
  | num n => num n
  | var y => if x = y then xa else var y
  | add a1 a2 => add (subst x xa a1) (subst x xa a2)
  | sub a1 a2 => sub (subst x xa a1) (subst x xa a2)

example : subst "x" (num 3) (add (var "x") (var "y")) = add (num 3) (var "y") := rfl

theorem subst_aval : ∀ {x xa a}, aval (subst x xa a) s = aval a (s [x := aval xa s])
  := by
  intros x xa a
  induction a
  case num n => simp [subst, aval]
  case var y => simp [subst, aval]
                split
                case isTrue => simp [upd, *]
                case isFalse => simp [upd, *]; split <;> simp_all [aval]
  case add a1 a2 ih1 ih2 => simp_all [subst, aval]
  case sub a1 a2 ih1 ih2 => simp_all [subst, aval]


-- Boolean Expressions ---------------------------------------------

inductive Bexp where
  | Bc    : Bool -> Bexp
  | Bnot  : Bexp -> Bexp
  | Band  : Bexp -> Bexp -> Bexp
  | BLess : Aexp -> Aexp -> Bexp
  deriving Repr

open Bexp

class ToBexp (a : Type) where
  toBexp : a -> Bexp

@[simp]
instance : ToBexp Bool where
  toBexp := Bc

@[simp]
instance : ToBexp Bexp where
  toBexp (b) := b


def bval (b: Bexp) (st: State) : Bool :=
  match b with
  | Bc v        => v
  | Bnot b1     => ! bval b1 st
  | Band b1 b2  => bval b1 st && bval b2 st
  | BLess a1 a2 => aval a1 st < aval a2 st

def bsubst (x : Vname) (xa : Aexp) (b : Bexp) : Bexp :=
  match b with
  | Bc v        => Bc v
  | Bnot b'     => Bnot  (bsubst x xa b')
  | Band  b1 b2 => Band  (bsubst x xa b1) (bsubst x xa b2)
  | BLess a1 a2 => BLess (subst x xa a1) (subst x xa a2)

theorem subst_bval : ∀ {x xa b}, bval (bsubst x xa b) s = bval b (s [x := aval xa s]) := by
  intros x xa b
  induction b
  case Bc v       => simp_all [bsubst, bval]
  case Bnot b' ih => simp_all [bsubst, bval, ih]
  case Band b1 b2 ih1 ih2 => simp_all [bsubst, bval, ih1, ih2]
  case BLess a1 a2 => simp_all [bsubst, bval, subst_aval]

-- Commands ----------------------------------------------------------

inductive Com where
  | Skip   : Com
  | Assign : Vname -> Aexp -> Com
  | Seq    : Com   -> Com  -> Com
  | If     : Bexp  -> Com  -> Com -> Com
  | While  : Bexp  -> Com  -> Com
  deriving Repr

open Com

def bLess (a1 a2 : Aexp) : Bexp := Bexp.BLess a1 a2

infix:10 "<<"  => fun x y => Bexp.BLess (ToAexp.toAexp x) (ToAexp.toAexp y)
infix:10 "<~"  => Com.Assign
infixr:8 ";;"  => Com.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => Com.If b c1 c2
notation:12 "WHILE" b "DO" c "END" => Com.While b c

-----------------------------------------------------------------------------
-- Bigstep Semantics
-----------------------------------------------------------------------------

open Com

inductive BigStep : Com -> State -> State -> Prop where
  | Skip   : ∀ {st},
                BigStep Skip st st
  | Assign : ∀ {st a n},
                BigStep (Assign a n) st (st [a := aval n st])
  | Seq    : ∀ {c1 c2 st1 st2 st3},
                BigStep c1 st1 st2 -> BigStep c2 st2 st3 ->
                BigStep (Seq c1 c2) st1 st3
  | IfTrue : ∀ {b c1 c2 st st'},
                bval b st = true -> BigStep c1 st st' ->
                BigStep (If b c1 c2) st st'
  | IfFalse : ∀ {b c1 c2 st st'},
                bval b st = false -> BigStep c2 st st' ->
                BigStep (If b c1 c2) st st'
  | WhileFalse : ∀ {b c st},
                bval b st = false ->
                BigStep (While b c) st st
  | WhileTrue : ∀ {b c st st' st''},
                bval b st = true -> BigStep c st st' -> BigStep (While b c) st' st'' ->
                BigStep (While b c) st st''

notation:12 "⟨" c "," s "⟩ ==> " t  => BigStep c s t

-----------------------------------------------------------------------------
-- Floyd-Hoare Logic
-----------------------------------------------------------------------------

abbrev Assertion := State -> Prop

@[simp]
def Implies (p q : Assertion) := ∀ s, p s -> q s

notation:10 p " ⊆ " q => Implies p q

notation:10 p "[[ " x ":=" a "]]" => fun s => p (s [ x := (aval a s) ])
inductive FH : Assertion -> Com -> Assertion -> Prop where

  | Skip              : ∀ {p},
                          FH p Skip p

  | Assign            : ∀ {p x a},
                          FH (p [[ x := a ]]) (x <~ a) p

  | Seq               : ∀ {p c1 c2 q r},
                          FH p c1 q -> FH q c2 r ->
                          FH p (c1 ;; c2) r

  | If                : ∀ {p b c1 c2 q},
                        FH (fun s => p s /\   bval b s) c1 q -> FH (fun s => p s /\ ¬ bval b s) c2 q ->
                        FH p (If b c1 c2) q

  | While             : ∀ {p b c},
                        FH (fun s => p s /\ bval b s) c p ->
                        FH p (While b c) (fun s => p s /\ ¬ bval b s)

  | CnsL              : ∀ {p' p c q},
                        FH p c q ->
                        (p' ⊆ p) ->
                        FH p' c q

  | CnsR              : ∀ {p c q q'},
                        FH p c q ->
                        (q ⊆ q') ->
                        FH p c q'

notation:10 "⊢" " {{" p "}} " c " {{" q "}}" => FH p c q

/--------------------------------------------------------------------------------------------------
## Problem 1: Soundness of Floyd-Hoare Logic
----------------------------------------------------------------------------------------------------/

/-

Recall the definition of `Assertion` and `Legit` from lecture.

Ok, we *should* have called it `Legit`, not "Valid"! from lecture...

-/


-- @[simp]
def Legit (p: Assertion) (c: Com) (q: Assertion) :=
  ∀ s t, p s -> (⟨ c, s ⟩ ==> t) -> q t

notation:10 "⊧" " {{" p "}} " c " {{" q "}}" => Legit p c q


/- The following lemmas prove our rules for `Consequence` are `Valid` -/
theorem conseq_l_valid : ∀ { p' p q : Assertion} { c : Com},
  (p' ⊆ p) -> (⊧ {{ p }} c {{ q }}) -> (⊧ {{ p' }} c {{ q }}) := by
  simp []
  intros p' p q c p'p pcq s t p's c_s_t
  apply pcq
  apply p'p
  repeat assumption

theorem conseq_r_valid : ∀ { p q q' : Assertion} {c : Com},
  (⊧ {{ p }} c {{ q }}) -> ( q ⊆ q' ) -> (⊧ {{ p }} c {{ q' }}) := by
  simp []
  intros p q q' c p_c_q qq' s t ps c_s_t
  apply qq'
  apply p_c_q
  repeat assumption

/- Here is a proof that our rule for `Skip` is `Valid` -/
-- @[autogradedProof 5]
theorem skip_valid : ∀ {p}, ⊧ {{ p }} Skip {{ p }} := by
  sorry

/- Prove that our rule for `Assign` is `Valid` -/

-- @[autogradedProof 15]
theorem seq_valid : ∀ {p q r c1 c2},
  (⊧ {{p}} c1 {{q}}) -> ( ⊧ {{q}} c2 {{r}}) -> ( ⊧ {{p}} c1 ;; c2 {{ r }}) := by
  sorry

/- Prove that our rule for `If` is `Valid` -/
-- @[autogradedProof 15]
theorem if_valid : ∀ {b c1 c2 p q},
  ( ⊧ {{ λs => p s /\ bval b s }} c1 {{ q }}) ->
  ( ⊧ {{ λs => p s /\ ¬ bval b s }} c2 {{ q }}) ->
  ( ⊧ {{ p }} If b c1 c2 {{ q }}) := by
  sorry


/- Complete the proof that the `inv` holds no matter how many times you spin around the loop -/
-- @[autogradedProof 15]
theorem loop_inv {inv s t } :
  ( ⊧ {{ λ s => inv s /\ bval b s }} c {{ inv }} ) ->
  (⟨ WHILE b DO c END, s ⟩ ==> t) ->
  inv s ->
  inv t
  := by
  intros c_inv w_s_t inv_s
  generalize bob : (WHILE b DO c END) = wbc at w_s_t
  sorry

-- The following says that upon exit, the loop-condition `b` is false
theorem loop_exit {b c s t} : (⟨ While b c, s ⟩ ==> t) -> bval b t = false := by
  intros w_s_t
  generalize bob : (WHILE b DO c END) = wbc at w_s_t
  induction w_s_t  <;> simp_all []

/- Use the above to complete the proof that our rule for `While` is `Valid` -/
-- @[autogradedProof 10]
theorem while_valid : ∀ {b c inv},
  ( ⊧ {{ λ s => inv s /\ bval b s }} c {{ inv }} ) ->
  ( ⊧ {{ inv }} While b c {{ λ s => inv s /\ ¬ bval b s }} ) := by
  sorry

-- Use all the above theorems to prove the soundness of Floyd-Hoare Logic
-- @[autogradedProof 10]
theorem fh_sound : ∀ {p c q}, (⊢ {{ p }} c {{ q }}) -> ( ⊧ {{ p }} c {{ q }}) := by
  sorry

/- ------------------------------------------------------------------------------------------------
## Problem 2: Soundness of Verification Condition Generation
We will prove that if the `vc p c q` is valid, then ⊢ {{p}} c {{q}} and hence ⊧ {{p}} c {{q}}
-------------------------------------------------------------------------------------------------- -/

inductive ACom where
  | Skip   : ACom
  | Assign : Vname -> Aexp -> ACom
  | Seq    : ACom  -> ACom -> ACom
  | If     : Bexp  -> ACom -> ACom -> ACom
  | While  : Assertion -> Bexp  -> ACom -> ACom
open ACom

@[simp]
def pre (c: ACom) (q : Assertion) : Assertion :=
  match c with
  | ACom.Skip         => q
  | ACom.Assign x a   => ( q [[ x := a ]] )
  | ACom.Seq c1 c2    => pre c1 (pre c2 q)
  | ACom.If b c1 c2   => (λ s => if bval b s then pre c1 q s else pre c2 q s)
  | ACom.While i _ _  => i

@[simp]
def vc (c : ACom) (q : Assertion) : Prop :=
  match c with
  | ACom.Skip        => True
  | ACom.Assign _ _  => True
  | ACom.Seq c1 c2   => vc c1 (pre c2 q) /\ (vc c2 q)
  | ACom.If _ c1 c2  => vc c1 q /\ vc c2 q
  | ACom.While i b c => (∀ s, i s -> bval b s -> pre c i s) /\
                        (∀ s, i s -> ¬ bval b s -> q s) /\
                        vc c i

@[simp]
def erase (c : ACom) : Com :=
  match c with
  | ACom.Skip         => Com.Skip
  | ACom.Assign x a   => Com.Assign x a
  | ACom.Seq c1 c2    => Com.Seq     (erase c1) (erase c2)
  | ACom.If b c1 c2   => Com.If b    (erase c1) (erase c2)
  | ACom.While _ b c  => Com.While b (erase c)

theorem simp_if_true : ∀ {b : Bool} { x y : Prop }, ((if b then x else y) /\ b=true) -> x := by
  intros b x y
  cases b <;> simp []

theorem simp_if_false : ∀ {b : Bool} { x y : Prop }, ((if b then x else y) /\ b=false) -> y := by
  intros b x y
  cases b <;> simp []

theorem foo_true : ∀ { b : Bexp } { p1 p2 : Assertion},
  (λ s => (if bval b s = true then p1 s else p2 s) ∧ bval b s = true) ⊆ p1
  := by simp [Implies]; intros; simp_all []

theorem foo_false : ∀ { b : Bexp } { p1 p2 : Assertion},
  (λ s => (if bval b s = true then p1 s else p2 s) ∧ ¬ bval b s = true) ⊆ p2
  := by simp [Implies]; intros; simp_all []

/- Complete the following lemma relating `vc` and `pre`.
   HINT: Do the proof is "by induction" on the `c`.
-/

-- @[autogradedProof 25]
theorem vc_pre : ∀ {c q}, vc c q -> (⊢ {{ pre c q }} (erase c) {{ q }}) := by
  sorry

-- Use `fh_sound` and `vc_pre` to prove that `vc` is "sound"

-- @[autogradedProof 5]
theorem vc_sound : ∀ {c q}, vc c q -> (⊧ {{ pre c q }} erase c {{ q }}) := by
  sorry


--  Lets extend `vc` to check triples `{p} c {q}`, by generating a `vc' p c q` defined
@[simp]
def vc' (p : Assertion) (c : ACom) (q : Assertion) := (p ⊆ pre c q) /\ vc c q

-- Prove that `vc'` is sound, i.e. that `vc' p c q` implies `{p} c {q}` is legit
-- @[autogradedProof 10]
theorem vc'_sound : ∀ {p c q}, (vc' p c q) -> (⊧{{ p }} erase c {{ q }}) := by
  sorry

/- -----------------------------------------------------------------------------------------------
## Problem 3: Loop Invariants
Fill in the appropriate definitions of `inv0` and `inv1` needed to verify the below programs.
-------------------------------------------------------------------------------------------------- -/

namespace Problem3

notation:10 x "<~" e  => ACom.Assign x (ToAexp.toAexp e)
infixr:20 ";;"  => ACom.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => ACom.If b c1 c2
notation:12 "WHILE {-@" inv "@-}" b "DO" c "END" => ACom.While inv (ToBexp.toBexp b) c
notation:20 "[|" c "|]" => erase c
notation:10 "⊢" " {|" p "|}" c "{|" q "|}" => FH p (erase c) q
notation:10 "⊧" " {|" p "|}" c "{|" q "|}" => (⊧ {{p}} (erase c) {{q}})

def inv_3_1 : Assertion := λ (s: State) =>
  sorry

theorem foo : ∀ {x y : Nat}, 0 < x -> x - 1 + (y + 1) = x + y := by
  omega

-- @[autogradedProof 20]
theorem ex_3_1 :
  ⊧ {| tt |}
      (x <~ z) ;;
      (y <~ 0) ;;
      (WHILE {-@ inv_3_1 @-} (0 << x)  DO
        ((x <~ x - 1) ;;
         (y <~ y + 1))
      END)
    {| λs => s y = s z |}
  := by
  apply vc'_sound; simp_all [aval,upd,bval, inv_3_1]
  constructor <;> repeat constructor
  sorry
  sorry

def inv_sum : Assertion := λ (s: State) =>
  sorry

-- @[autogradedProof 40]
theorem ex_sum :
  ⊧ {| λs => s x = 10 |}
     (y <~ 1) ;;
     (z <~ 0) ;;
     (WHILE {-@ inv_sum @-} (y << x) DO
       (z <~ z + y) ;;
       (y <~ y + 1)
     END)
    {| λ s => s z == 45 |}
  := by
  apply vc'_sound; simp_all [aval,upd, bval, inv_sum]
  constructor <;> repeat constructor
  sorry
  sorry
