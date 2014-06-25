Require Import String.

Section string_dec.

  (* The goal of this section is to prove the following theorem:
     string_dec_refl l : string_dec l l = left (eq_refl l)
   *)

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

Section types.
  (* Object types are records of types, we define them as association lists *)

  Inductive type :=
  | Empty_type
  | Cons_type : string -> type -> type -> type.

  (* Alternative constructor used for notation purpose *)
  Definition Cons_type_2 : (string * type) -> type -> type :=
    fun f B => let (l, A) := f in Cons_type l A B.
End types.

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

Section objects.
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

  Definition Obj A := Preobject A (assoc A) (domain A).

  (* End of the axiomatisation of methods: Method A B is equivalent to Obj A -> Obj B. *)
  Parameter Eval_meth : forall A B, Method A B -> Obj A -> Obj B.
  Parameter Make_meth : forall A B, (Obj A -> Obj B) -> Method A B.
  Axiom beta : forall A B f a, Eval_meth A B (Make_meth A B f) a = f a.

  (* We will often need to test wether a label is in a domain
     so we reimplement the decidable membership test on lists of strings. *)
  Fixpoint in_dom l d :=
    match d with
      | nil => false
      | cons l2 d =>
        if (string_dec l l2) then true else in_dom l d
    end.
End objects.

Delimit Scope object_scope with obj.
Delimit Scope method_scope with meth.

Bind Scope method_scope with Method.
Bind Scope object_scope with Preobject.

Notation "l = 'ς' ( x !: A ) m" :=
  (existT (fun l2 => Method A (assoc A l2)) l%string (Make_meth A (assoc A l) (fun x => m%obj)))
    (at level 50) : method_scope.

Notation "l ∈ d" := (in_dom l d = true) (at level 60).
Notation "l ∉ d" := (~ l ∈ d) (at level 60).

Section semantics.
  (* Selection and update go inside objects so they have to be defined on preobjects first. *)

  Definition empty_object := poempty Empty_type (assoc Empty_type).

  (* Properties of ∈ *)
  Lemma not_in_nil l : l ∉ nil.
  Proof.
    discriminate.
  Defined.

  Lemma in_cons_hd l d : l ∈ (cons l d).
  Proof.
    simpl.
    rewrite (string_dec_refl l).
    reflexivity.
  Defined.

  Lemma in_cons_tl l1 l2 d : l1 ∈ d -> l1 ∈ (cons l2 d).
  Proof.
    simpl.
    intro e.
    rewrite e.
    case (string_dec l1 l2) ; reflexivity.
  Defined.

  (* preselect was actually defined in proof mode like this: *)

  Fixpoint preselect l A f d (po : Preobject A f d) :
    l ∈ d -> Obj A -> Obj (f l).
  Proof.
    destruct po as [ | A f d l2 m tail ].
    - intro H.
      destruct (not_in_nil l H).
    - simpl.
      case (string_dec l l2).
      + intros e _.
        destruct e.
        apply Eval_meth.
        assumption.
      + intro.
        apply preselect.
        assumption.
  Defined.

  Definition select l A a (H : l ∈ (domain A)) : Obj (assoc A l) :=
    preselect l A (assoc A) (domain A) a H a.

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

  (* Specification of select: *)

  Theorem presel_cons_eq l A f d m1 po : preselect l A f (cons l d) (pocons A f d l m1 po) (in_cons_hd l d) = Eval_meth _ _ m1.
  Proof.
    simpl.
    unfold in_cons_hd.
    rewrite (string_dec_refl).
    reflexivity.
  Qed.

  Theorem presel_cons_diff l l2 A f d m1 po H :
    l <> l2 ->
    preselect l A f (cons l2 d) (pocons A f d l2 m1 po) (in_cons_tl l l2 d H)
    = preselect l A f d po H.
  Proof.
    intro diff.
    simpl.
    unfold in_cons_tl.
    case (string_dec l l2).
    - intro eq.
      destruct (diff eq).
    - intro diff2.
      apply f_equal.
      case H.
      reflexivity.
  Qed.

  (* Specification of update: *)

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
End semantics.

Notation "a # l" := (select l%string _ a%obj eq_refl) (at level 50) : object_scope.
Notation "o ## l ⇐ 'ς' ( x !: A ) m" := (update A l%string o (Make_meth A (assoc A l) (fun x => m))) (at level 50).

Section init.
  Definition preinit A d :
    (forall l, l ∈ d -> l ∈ domain A) ->
    Preobject A (assoc A) d.
  Proof.
    induction d as [ | l d ].
    - intro.
      apply poempty.
    - intro H.
      apply pocons.
      + apply Make_meth.
        intro a.
        apply select.
        * exact a.
        * apply H.
          apply in_cons_hd.
      + apply IHd.
        intros l1 H1.
        apply H.
        apply in_cons_tl.
        assumption.
  Defined.

  Definition init A : Obj A := preinit A (domain A) (fun _ H => H).
End init.

(* Definition of objects without respecting the order of labels given by the type. *)
Definition pocons_3 A (lm : sigT (fun l2 => Method A (assoc A l2))) (a : Obj A) :
  Obj A :=
  let (l, m) := lm in
  update A l a m.

Notation "[ m1 ; .. ; mn ]" := (pocons_3 _ m1%meth (.. (pocons_3 _ mn%meth (init _)) .. )) : object_scope.

Section examples.
  (* Encodding of booleans *)
  Definition Bool A : type :=
    [ "if" : A ; "then" : A ; "else" : A ]%ty.

  Definition true A : Obj (Bool A) :=
    [ "if" = ς(x !: Bool A) (x#"then") ]%obj.

  Definition false A : Obj (Bool A) :=
    [ "if" = ς(x !: Bool A) (x#"else") ]%obj.

  Theorem true_select A : ((true A)#"if")%obj = ((true A)#"then")%obj.
  Proof.
    unfold select.
    simpl.
    rewrite beta.
    reflexivity.
  Qed.

  Definition Ifthenelse A b t e :=
    (((b##"then" ⇐ ς(x !: Bool A) t)##"else" ⇐ ς(x !: Bool A) e)#"if")%obj.

  Notation "'IF' b 'THEN' t 'ELSE' e" := (Ifthenelse _ b t e) (at level 50) : object_scope.

  Theorem if_true A b c : Ifthenelse A (true A) b c = b.
  Proof.
    unfold Ifthenelse.
    unfold update.
    simpl.
    unfold select.
    simpl.
    rewrite beta.
    simpl.
    rewrite beta.
    reflexivity.
  Qed.

  Theorem if_false A b c : Ifthenelse A (false A) b c = c.
  Proof.
    unfold Ifthenelse.
    unfold update.
    simpl.
    unfold select.
    simpl.
    rewrite beta.
    simpl.
    rewrite beta.
    reflexivity.
  Qed.

  (* Encodding of the simply-typed λ-calculus *)

  Definition Arrow A B :=
    [ "arg" : A ; "val" : B ]%ty.

  Infix "→" := Arrow (at level 50).

  Definition Lambda A B (f : Obj A -> Obj B) : Obj (A → B) :=
    [ "val" = ς(x !: A → B) (f (x#"arg")) ]%obj.

  Notation "'λ' ( x !: A ) b" := (Lambda A _ (fun x : Obj A => b)) (at level 50).

  Definition App A B (f : Obj (A → B)) (a : Obj A) : Obj B :=
    ((f##"arg" ⇐ ς(x !: A → B) a)#"val")%obj.

  Infix "@" := (App _ _) (at level 50).

  Theorem beta_red A B f c : (Lambda A B f) @ c = f c.
  Proof.
    unfold Lambda, App.
    unfold update, select.
    simpl ; rewrite beta.
    apply f_equal.
    simpl ; rewrite beta.
    reflexivity.
  Qed.
End examples.

Section subtyping.
  (* We define directly type_dec instead of using the decide equality tactic
     in order to get an easier proof of type_dec_refl. *)

  Lemma diff_empty_cons l A B : Empty_type <> Cons_type l A B.
  Proof.
    discriminate.
  Defined.

  Lemma diff_cons_empty l A B : Cons_type l A B <> Empty_type.
  Proof.
    discriminate.
  Defined.

  Lemma eq_cons_cons lA A1 A2 lB B1 B2 : lA = lB -> A1 = B1 -> A2 = B2 -> Cons_type lA A1 A2 = Cons_type lB B1 B2.
  Proof.
    intros.
    destruct H.
    destruct H0.
    destruct H1.
    reflexivity.
  Defined.

  Definition eq_cons_cons_1 C :=
    match C with
      | Empty_type => ""%string
      | Cons_type l _ _ => l
    end.

  Definition eq_cons_cons_2 C :=
    match C with
      | Empty_type => Empty_type
      | Cons_type _ A _ => A
    end.

  Definition eq_cons_cons_3 C :=
    match C with
      | Empty_type => Empty_type
      | Cons_type _ _ A => A
    end.

  Fixpoint type_dec (A B : type) : {A = B} + {A <> B} :=
    match A with
      | Empty_type =>
        match B with
          | Empty_type => left eq_refl
          | Cons_type lB B1 B2 => right (diff_empty_cons lB B1 B2)
        end
      | Cons_type lA A1 A2 =>
        match B with
          | Empty_type => right (diff_cons_empty lA A1 A2)
          | Cons_type lB B1 B2 =>
            match string_dec lA lB with
              | left el =>
                match type_dec A1 B1 with
                  | left e1 =>
                    match type_dec A2 B2 with
                      | left e2 =>
                        left (eq_cons_cons lA A1 A2 lB B1 B2 el e1 e2)
                      | right n2 =>
                        right
                          (fun H : Cons_type lA A1 A2 = Cons_type lB B1 B2 =>
                             n2 (f_equal eq_cons_cons_3 H))
                    end
                  | right n1 =>
                    right
                      (fun H : Cons_type lA A1 A2 = Cons_type lB B1 B2 =>
                         n1 (f_equal eq_cons_cons_2 H))
                end
              | right nl =>
                right
                  (fun H : Cons_type lA A1 A2 = Cons_type lB B1 B2 =>
                     nl (f_equal eq_cons_cons_1 H))
            end
        end
    end.

  Theorem type_dec_refl A : type_dec A A = left (eq_refl A).
  Proof.
    induction A.
    - reflexivity.
    - simpl.
      rewrite string_dec_refl.
      rewrite IHA1.
      rewrite IHA2.
      reflexivity.
  Qed.

  (* Definition of the subtyping relation: A <: B if B is a subset of A. *)
  Fixpoint Subtype A B :=
    match B with
      | Empty_type => True
      | Cons_type l B1 B2 =>
        l ∈ domain A /\ B1 = assoc A l /\ Subtype A B2
    end.

  Infix "<:" := Subtype (at level 60).

  Lemma subtype_cons A B l C :
    A <: B ->
         l ∉ domain A ->
         Cons_type l C A <: B.
  Proof.
    induction B ; intros.
    - exact I.
    - simpl.
      destruct H as (H1, H2).
      case (string_dec s l) ; intro.
      + destruct e.
        destruct (H0 H1).
      + intuition.
  Qed.

  Section subtype_reflexivity.

    (* Unfortunately, the theorem forall A, A <: A is false
       when A has several occurences of the same label *)
    (* Hence we can only prove it for well-formed types: types without duplicates. *)
    Fixpoint well_formed_type A :=
      match A with
        | Empty_type => True
        | Cons_type l A1 A2 => l ∉ domain A2 /\ well_formed_type A2
      end.

    Theorem well_formed_dec A : {well_formed_type A} + {~ well_formed_type A}.
    Proof.
      induction A.
      - left.
        exact I.
      - simpl.
        destruct IHA2.
        + case (in_dom s (domain A2)).
          * right.
            intro H.
            destruct H as (H, _).
            destruct (H eq_refl).
          * left.
            split ; [discriminate | exact w].
        + right.
          intro H.
          destruct H as (H1, H2).
          exact (n H2).
    Defined.

    Theorem subtype_refl A : well_formed_type A -> A <: A.
    Proof.
      intro.
      induction A.
      - exact I.
      - simpl in *.
        split.
        + rewrite string_dec_refl.
          reflexivity.
        + rewrite string_dec_refl.
          split.
          reflexivity.
          destruct H.
          apply subtype_cons.
          * apply IHA2.
            assumption.
          * assumption.
    Defined.
  End subtype_reflexivity.

  (* The goal of the reminding of this section is to define a function
     coerce : forall A B, A <: B -> Obj A -> Obj B *)

  Lemma precast A B d : Obj A -> (forall l, l ∈ d -> l ∈ domain A) -> Preobject B (assoc A) d.
  Proof.
    intros a H.
    induction d as [ |  l d].
    - apply poempty.
    - apply pocons.
      + apply Make_meth.
        intro self.
        apply select.
        * exact a.
        * apply (H l).
          simpl.
          rewrite string_dec_refl.
          reflexivity.
      + apply IHd.
        intros.
        apply H.
        simpl.
        rewrite H0.
        case (string_dec l0 l) ; reflexivity.
  Defined.

  Lemma domain_subtype A B l : A <: B -> l ∈ domain B -> l ∈ domain A.
  Proof.
    induction B ; simpl.
    - discriminate.
    - intro H ; destruct H as (H1, (H2, H3)).
      case (string_dec l s) ; intros.
      + destruct e.
        assumption.
      + apply IHB2.
        * assumption.
        * assumption.
  Defined.

  Definition ocast A B : A <: B -> Obj A -> Preobject B (assoc A) (domain B).
  Proof.
    intros.
    apply precast.
    - assumption.
    - intro l.
      apply domain_subtype ; assumption.
  Defined.

  Lemma meth_eq A B1 B2 : B2 = B1 -> Method A B1 -> Method A B2.
    intros.
    rewrite H.
    assumption.
  Defined.

  Lemma coerce_1 A f g d : (forall l, l ∈ d -> f l = g l) -> Preobject A f d -> Preobject A g d.
  Proof.
    intros.
    induction X.
    - apply poempty.
    - apply pocons.
      + assert (Method A (f l) = Method A (g l)).
        * apply f_equal.
          apply H.
          apply in_cons_hd.
        * rewrite H0 in m.
          assumption.
      + apply IHX.
        intros.
        apply (H l0).
        apply in_cons_tl.
        assumption.
  Defined.

  Lemma assoc_subtype A B l : A <: B -> l ∈ domain B -> assoc A l = assoc B l.
  Proof.
    intro.
    induction B.
    - intro H0.
      apply not_in_nil in H0.
      destruct H0.
    - simpl.
      case (string_dec l s) ; intro.
      + destruct e.
        destruct H as (_, (H, _)).
        symmetry.
        assumption.
      + apply IHB2.
        destruct H as (_, (_, H)).
        assumption.
  Defined.

  Definition coerce A B : A <: B -> Obj A -> Obj B.
  Proof.
    intros.
    apply (coerce_1 B (assoc A) (assoc B) (domain B)).
    - intros.
      apply assoc_subtype ; assumption.
    - apply ocast ; assumption.
  Defined.
End subtyping.


Definition add_loop A d l : l ∈ domain A ->
                            Preobject A (assoc A) d -> Preobject A (assoc A) (cons l d).
Proof.
  intros Hd a.
  apply pocons.
  - apply Make_meth.
    intro self.
    apply select ; assumption.
  - assumption.
Defined.

Definition preupdate_inversion A f d l : l ∈ domain A ->
                                         f = assoc A ->
                                         forall a,
                                         l ∈ d ->
                                         exists m b,
                                           a = preupdate l A f d b m.
Proof.
  intros HdA Hf a.
  induction a as [ | A f d l1 m a ].
  - simpl.
    discriminate.
  - simpl.
    case (string_dec l l1).
    + intros e _.
      destruct e.
      symmetry in Hf.
      destruct Hf.
      exists m.
      exists (add_loop A d l HdA a).
      unfold add_loop.
      rewrite preup_cons_eq.
      reflexivity.
    + intros ldiff Hd.
      destruct (IHa HdA Hf Hd) as (m1, (b1, H1)).
      exists m1.
      exists (pocons A f d l1 m b1).
      rewrite preup_cons_diff.
      * rewrite H1.
        reflexivity.
      * assumption.
Defined.

Definition update_inversion A a l : l ∈ domain A ->
                                    exists m b, a = update A l b m :=
  fun Hd =>
    preupdate_inversion A (assoc A) (domain A) l Hd (eq_refl) a Hd.
