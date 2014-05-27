Require Import String.

Section string_dec.

  (* The goal of this section is to prove the following theorem:
     string_dec_refl l : string_dec l l = left (eq_refl l)
   *)

  Lemma eq_rect_refl A a (P : A -> Type) (H : P a) :
    @eq_rect_r A a P H a eq_refl = H.
  Proof.
    reflexivity.
  Qed.

  Theorem bool_dec_refl b : Bool.bool_dec b b = left (eq_refl b).
  Proof.
    induction b ; reflexivity.
  Qed.

  Theorem ascii_dec_refl a : Ascii.ascii_dec a a = left (eq_refl a).
  Proof.
    induction a.
    unfold Ascii.ascii_dec, Ascii.ascii_rec, Ascii.ascii_rect.
    repeat rewrite bool_dec_refl.
    reflexivity.
  Qed.

  Lemma string_dec_cons_eq1 a l :
    string_dec (String a l) (String a l) =
    match Ascii.ascii_dec a a with
      | left a0 =>
        eq_rec_r
          (fun a' => {String a' l = String a l} + {String a' l <> String a l})
          match string_dec l l with
            | left a3 =>
              eq_rec_r
                (fun s => {String a s = String a l} + {String a s <> String a l})
                (left eq_refl) a3
            | right diseq =>
              right
                (fun absurd : String a l = String a l =>
                   diseq
                     (f_equal
                        (fun e =>
                           match e with
                             | ""%string => l
                             | String _ s => s
                           end) absurd))
          end a0
      | right diseq =>
        right
          (fun absurd : String a l = String a l =>
             diseq
               (f_equal
                  (fun e =>
                     match e with
                       | ""%string => a
                       | String a _ => a
                     end) absurd))
    end.
  Proof.
    reflexivity.
  Qed.

  Lemma string_dec_cons_eq2 a l :
    string_dec (String a l) (String a l) =
    match string_dec l l with
      | left a3 =>
        eq_rec_r
          (fun s => {String a s = String a l} + {String a s <> String a l})
          (left eq_refl) a3
      | right diseq =>
        right
          (fun absurd : String a l = String a l =>
             diseq
               (f_equal
                  (fun e =>
                     match e with
                       | ""%string => l
                       | String _ s => s
                     end) absurd))
    end.
  Proof.
    rewrite string_dec_cons_eq1.
    rewrite ascii_dec_refl.
    reflexivity.
  Qed.

  Theorem string_dec_refl l : string_dec l l = left (eq_refl l).
  Proof.
    induction l.
    - reflexivity.
    - rewrite string_dec_cons_eq2.
      rewrite IHl.
      reflexivity.
  Qed.
End string_dec.

(* Object types are records of types, we define them as association lists *)

Inductive type :=
| Empty_type
| Cons_type : string -> type -> type -> type.

(* Alternative constructor used for notation purpose *)
Definition Cons_type_2 : (string * type) -> type -> type :=
  fun f B => let (l, A) := f in Cons_type l A B.

(* Scope of object types *)
Bind Scope obj_type_scope with type.
Delimit Scope obj_type_scope with ty.
(* Scope of object type fields (pairs of strings and types) *)
Delimit Scope type_field_scope with tf.

(* Notations for object types:
   [ "l₁" : A₁ ; "l₂" : A₂ ; … ; "lₙ" : Aₙ ]
 *)
Notation "l : A" := (l%string, A) (at level 50) : type_field_scope.
Notation "[ x1 ; .. ; xn ]" :=
  (Cons_type_2 x1%tf .. (Cons_type_2 xn%tf Empty_type) ..) : obj_type_scope.


(* Objects are records of methods.
   A well-typed object of type A = [ lᵢ : Aᵢ ]
   is of the form [ lᵢ = ς(x !: A) tᵢ ] where x : A ⊢ tᵢ : Aᵢ

   The type A appears 3 times in the definition of well-typed object of type A :
    - in each ς binder
    - to type each tᵢ
    - to list the labels

   Since we cannot construct an object without breaking the invariant, we define
   preobjects of type (A, f, d) such that Obj A = Preobject (A, assoc A, domain A).

 *)

Fixpoint assoc (A : type) : string -> type :=
  fun l =>
    match A with
      | Empty_type => Empty_type
      | Cons_type l2 B C =>
        match string_dec l l2 with
          | left _ => B
          | right _ => assoc C l
        end
    end.

Fixpoint domain A :=
  match A with
    | Empty_type => nil
    | Cons_type l _ C => cons l (domain C)
  end.

(* We have to axiomatize the type of methods because
   Method A B := Obj A -> Obj B has a negative occurence of Obj which blocks
   the recursive definition
 *)

Parameter Method : type -> type -> Type.

Inductive Preobject : type -> (string -> type) -> list string -> Type :=
| poempty : forall A f, Preobject A f nil
| pocons : forall A f d (l : string),
             Method A (f l) ->
             Preobject A f d ->
             Preobject A f (cons l d).

Definition Obj A := Preobject A (assoc A) (domain A).

Parameter Eval_meth : forall A B, Method A B -> Obj A -> Obj B.
Parameter Make_meth : forall A B, (Obj A -> Obj B) -> Method A B.
Axiom beta : forall A B f a, Eval_meth A B (Make_meth A B f) a = f a.

(* For notation purpose, we construct objects using couples of labels and methods *)
Definition pocons2 A f d (lm : sigT (fun l2 => Method A (f l2))) (po : Preobject A f d) :
  let (l, _) := lm in
  Preobject A f (cons l d) :=
  let (l, m) as s return (let (l, _) := s in Preobject A f (l :: d)) := lm in
  pocons A f d l m po.

Delimit Scope object_scope with obj.
Delimit Scope method_scope with meth.

Bind Scope method_scope with Method.
Bind Scope object_scope with Preobject.

Notation "l = 'ς' ( x !: A ) m" :=
  (existT (fun l2 => Method A (assoc A l2)) l%string (Make_meth A (assoc A l) (fun x => m%obj)))
    (at level 50) : method_scope.
Notation "[ m1 ; .. ; mn ]" := (pocons2 _ _ _ m1%meth (.. (pocons2 _ _ _ mn%meth (poempty _ _)) .. )) : object_scope.

(* Since the calculus is not SN, we also axiomatize loops *)

Parameter loop : forall A, Obj A.

(* Selection and update go inside objects so they have to be defined on preobjects first. *)

Fixpoint preselect l A f d (po : Preobject A f d) : Obj A -> Obj (f l) :=
  match po with
    | poempty _ _ => (fun _ => loop _)
    | pocons A f d l2 m tail =>
      match string_dec l l2 with
        | left e =>
          Eval_meth _ _
                    (eq_rect_r (fun l1 => Method A (f l1)) m e)
        | right _ => preselect _ _ _ _ tail
      end
  end.

Fixpoint select l A a : Obj (assoc A l) :=
  preselect l A (assoc A) (domain A) a a.
Notation "a # l" := (select l%string _ a%obj) (at level 50) : object_scope.

Fixpoint preupdate l (A : type) (f : string -> type) (d : list string)
         (po : Preobject A f d) :
  Method A (f l) -> Preobject A f d :=
  match
    po
  with
    | poempty A f => fun _ => poempty A f
    | pocons A f d l1 m p =>
      fun m1 =>
        match
          string_dec l l1
        with
          | left e =>
            pocons A f d l1
                   (eq_rect l (fun l2 => Method A (f l2)) m1 l1 e) p
          | right n =>
            pocons A f d l1 m (preupdate l A f d p m1)
        end
  end.

Definition update A l (a : Obj A) m :=
  preupdate l A (assoc A) (domain A) a m.

Notation "o ## l ⇐ 'ς' ( x !: A ) m" := (update A l%string o (Make_meth A (assoc A l) (fun x => m))) (at level 50).

(* Specification of select: *)
(* - preselect l A f (cons l d) (pocons A f d l m1 po) = Eval_meth m1 *)
(* - l <> l2 -> preselect l A f (cons l2 d) (pocons A f d l2 m1 po) m2 = preselect l A f d po *)

Theorem presel_cons_eq l A f d m1 po : preselect l A f (cons l d) (pocons A f d l m1 po) = Eval_meth _ _ m1.
Proof.
  unfold preselect.
  rewrite string_dec_refl.
  reflexivity.
Qed.

Theorem presel_cons_diff l l2 A f d m1 po :
  l <> l2 ->
  preselect l A f (cons l2 d) (pocons A f d l2 m1 po)
  = preselect l A f d po.
Proof.
  intro diff.
  unfold preselect.
  case (string_dec l l2).
  - intro eq.
    destruct (diff eq).
  - intro diff2.
    reflexivity.
Qed.

(* Specification of update: *)
(* - preupdate l A f nil (poempty A f) m = poempty A f *)
(* - preupdate l A f (cons l d) (pocons A f d l m1 po) m2 = pocons A f d l m2 po *)
(* - l <> l2 -> preupdate l A f (cons l2 d) (pocons A f d l2 m1 po) m2 = pocons A f d l2 m1 (preupdate l A f d po m1) *)

Theorem preup_empty A f l m : preupdate l A f nil (poempty A f) m = poempty A f.
Proof.
  reflexivity.
Qed.

Theorem preup_cons_eq A f d l po m1 m2 : preupdate l A f (cons l d) (pocons A f d l m1 po) m2 = pocons A f d l m2 po.
Proof.
  unfold preupdate.
  rewrite string_dec_refl.
  apply f_equal2 ; reflexivity.
Qed.

Theorem preup_cons_diff A f d l l2 m1 m2 po :
  l <> l2 ->
  preupdate l A f (cons l2 d) (pocons A f d l2 m1 po) m2
  = pocons A f d l2 m1 (preupdate l A f d po m2).
Proof.
  unfold preupdate.
  intro diff.
  case (string_dec l l2).
  - intro eq.
    destruct (diff eq).
  - intro diff2.
    reflexivity.
Qed.

(* Examples *)
(* Encodding of booleans *)
Definition Bool A : type :=
  [ "if" : A ; "then" : A ; "else" : A ]%ty.

Definition true A : Obj (Bool A) :=
  [ "if" = ς(x !: Bool A) (x#"then") ;
    "then" = ς(x !: Bool A) (x#"then") ;
    "else" = ς(x !: Bool A) (x#"else") ]%obj.

Definition false A : Obj (Bool A) :=
  [ "if" = ς(x !: Bool A) (x#"else") ;
    "then" = ς(x !: Bool A) (x#"then") ;
    "else" = ς(x !: Bool A) (x#"else") ]%obj.

Theorem true_select A : ((true A)#"if")%obj = ((true A)#"then")%obj.
Proof.
  reflexivity.
Qed.

Definition Ifthenelse A b t e :=
  (((b##"then" ⇐ ς(x !: Bool A) t)##"else" ⇐ ς(x !: Bool A) e)#"if")%obj.

Notation "'IF' b 'THEN' t 'ELSE' e" := (Ifthenelse _ b t e) (at level 50) : object_scope.

Theorem if_true A b c : Ifthenelse A (true A) b c = b.
Proof.
  unfold Ifthenelse.
  simpl.
  rewrite eq_rect_refl.
  rewrite beta.
  simpl.
  rewrite eq_rect_refl.
  rewrite beta.
  reflexivity.
Qed.

Theorem if_false A b c : Ifthenelse A (false A) b c = c.
Proof.
  unfold Ifthenelse.
  simpl.
  rewrite eq_rect_refl.
  rewrite beta.
  simpl.
  rewrite eq_rect_refl.
  rewrite beta.
  reflexivity.
Qed.

(* Encodding of the simply-typed λ-calculus *)

Definition Arrow A B :=
  [ "arg" : A ; "val" : B ]%ty.

Infix "→" := Arrow (at level 50).

Definition Lambda A B (f : Obj A -> Obj B) : Obj (A → B) :=
  [ "arg" = ς(x !: A → B) (x#"arg") ;
    "val" = ς(x !: A → B) (f (x#"arg")) ]%obj.

Notation "'λ' ( x !: A ) b" := (Lambda A _ (fun x : Obj A => b)) (at level 50).

Definition App A B (f : Obj (A → B)) (a : Obj A) : Obj B :=
  ((f##"arg" ⇐ ς(x !: A → B) a)#"val")%obj.

Infix "@" := (App _ _) (at level 50).

Theorem beta_red A B f c : (Lambda A B f) @ c = f c.
Proof.
  unfold Lambda, App.
  simpl ; rewrite eq_rect_refl ; rewrite beta.
  apply f_equal.
  simpl ; rewrite eq_rect_refl ; rewrite beta.
  reflexivity.
Qed.
