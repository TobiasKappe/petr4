Require Export Coq.Lists.List.
Export ListNotations.
Require Export Coq.Bool.Bool.
Require Export P4light.Utiliser.

(** Notation entries. *)
Declare Custom Entry p4type.

Reserved Notation "∫ ty1 ≡ ty2"
         (at level 200, ty1 custom p4type, ty2 custom p4type, no associativity).

Declare Custom Entry p4uop.
Declare Custom Entry p4bop.
Declare Custom Entry p4matchkind.
Declare Custom Entry p4hdr_op.
Declare Custom Entry p4expr.
Declare Custom Entry p4stmt.
Declare Custom Entry p4decl.
Declare Custom Entry p4ctrldecl.
Declare Custom Entry p4topdecl.

(** * Definitions and Lemmas regarding Fields *)
Module Field.
  Section FieldTypes.

    Variable (tags_t : Type).

    (** Field type. *)
    Definition f (T : Type) : Type := (string tags_t) * T.

    (** Fields. *)
    Definition fs (T : Type) : Type := list (f T).
  End FieldTypes.

  Section FieldLibrary.
    Context {tags_t : Type}.

    (** Predicate on a field's data. *)
    Definition predf_data {T : Type} (P : T -> Prop) : f tags_t T -> Prop :=
      fun '(_, t) => P t.
    (**[]*)

    (** Predicate over every data in fields. *)
    Definition predfs_data {T : Type} (P : T -> Prop) : fs tags_t T -> Prop :=
      Forall (predf_data P).
    (**[]*)

    (** Relation betwixt two field instances. *)
    Definition relf {U V : Type}
               (R : U -> V -> Prop) : f tags_t U -> f tags_t V -> Prop :=
      fun u v => P4String.equiv (fst u) (fst v) /\ R (snd u) (snd v).
    (**[]*)

    (** Relation between two instances of fields. *)
    Definition relfs {U V : Type}
               (R : U -> V -> Prop) : fs tags_t U -> fs tags_t V -> Prop :=
      Forall2 (relf R).
    (**[]*)

    (** A predicate from a relation between fields. *)
    Definition relf_pred {U V : Type}
    {R1 : U -> V -> Prop} {R2 : U -> V -> Prop}
    {u : f tags_t U} {v : f tags_t V}
    (Q : forall (u' : U) (v' : V), R1 u' v' -> R2 u' v')
    (H : relf R1 u v) :=
      match H with
      | conj Hname HR1 => conj Hname (Q (snd u) (snd v) HR1)
      end.
    (**[]*)

    (** Filter. *)
    Definition filter {U : Type} (f : U -> bool) : fs tags_t U -> fs tags_t U :=
      List.filter (f ∘ snd).
    (**[]*)

    (** Map. *)
    Definition map {U V : Type} (f : U -> V) : fs tags_t U -> fs tags_t V :=
      List.map (fun '(x,u) => (x, f u)).
    (**[]*)

    (** Fold. *)
    Definition fold {U V : Type} (f : string tags_t -> U -> V -> V)
               (fds : fs tags_t U) (init : V) : V :=
      List.fold_right (fun '(x,u) acc => f x u acc) init fds.
    (**[]*)

    (** Member access. *)
    Fixpoint get {U : Type} (x : string tags_t)
             (fds : fs tags_t U) : option U :=
      match fds with
      | []            => None
      | (x',u') :: fds => if equiv_dec x x' then Some u'
                        else get x fds
      end.

    (** Member update. *)
    Fixpoint update {U : Type} (x : string tags_t) (u : U)
             (fds : fs tags_t U) : fs tags_t U :=
      match fds with
      | [] => []
      | (x',u') :: fds => (x', if equiv_dec x x' then u else u') :: update x u fds
      end.
    (**[]*)
  End FieldLibrary.

  Module FieldTactics.
    Ltac invert_predf :=
      match goal with
      | H:predf_data _ _ |- _ => inv H
      end.
    (**[]*)

    Ltac invert_cons_predfs :=
      match goal with
      | H:predfs_data _ (_::_) |- _ => inv H
      end.
    (**[]*)

    Ltac invert_nil_cons_relate :=
      match goal with
      | H:relfs _ [] (_::_) |- _ => inversion H
      | H:relfs _ (_::_) [] |- _ => inversion H
      end.
    (**[]*)

    Ltac invert_relf :=
      match goal with
      | H:relf _ _ _ |- _ => inv H
      end.
    (**[]*)

    Ltac invert_cons_cons_relate :=
      match goal with
      | H:relfs _ (_::_) (_::_) |- _ => inv H; unfold relf in *
      end.
    (**[]*)
  End FieldTactics.
End Field.

(** * P4light AST *)
Module P4light.
  Module F := Field.

  (** Function call parameters/arguments. *)
  Inductive paramarg (A B : Type) : Type :=
  | PAIn (a : A)
  | PAOut (b : B)
  | PAInOut (b : B).

  Arguments PAIn {_} {_}.
  Arguments PAOut {_} {_}.
  Arguments PAInOut {_} {_}.

  (** Relating [paramarg]s. *)
  Definition rel_paramarg {A1 A2 B1 B2 : Type}
             (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
             (pa1 : paramarg A1 B1)
             (pa2 : paramarg A2 B2) : Prop :=
    match pa1, pa2 with
    | PAIn a1, PAIn a2       => RA a1 a2
    | PAOut b1, PAOut b2
    | PAInOut b1, PAInOut b2 => RB b1 b2
    | _, _ => False
    end.
  (**[]*)

  Definition rel_paramarg_same
             {A B : Type} (R : A -> B -> Prop)
             (paa : paramarg A A) (pab : paramarg B B) : Prop :=
    rel_paramarg R R paa pab.
  (**[]*)

  (** Function signatures/instantiations. *)
  Inductive arrow (tags_t A B R : Type) : Type :=
    Arrow (pas : F.fs tags_t (paramarg A B)) (returns : option R).
  (**[]*)

  Arguments Arrow {_} {_} {_} {_}.

  (** Directions. *)
  Module Dir.
    Inductive d : Set :=
      | DIn    (* in *)
      | DOut   (* out *)
      | DInOut (* inout *)
      | DZilch (* no direction *).
    (**[]*)
  End Dir.

  (** * Expression Grammar *)
  Module Expr.
    Import Dir.

    Section P4Types.
      Variable (tags_t : Type).

      (** Expression types. *)
      Inductive t : Type :=
      | TBool                            (* bool *)
      | TBit (width : positive)          (* unsigned integers *)
      | TInt (width : positive)          (* signed integers *)
      | TError                           (* the error type *)
      | TMatchKind                       (* the matchkind type *)
      | TRecord (fields : F.fs tags_t t) (* the record and struct type *)
      | THeader (fields : F.fs tags_t t) (* the header type *)
      | THeaderStack (fields : F.fs tags_t t)
                     (size : positive)   (* header stack type *).
      (**[]*)

      (** Function parameters. *)
      Definition params : Type := F.fs tags_t (paramarg t t).

      (** Function types. *)
      Definition arrowT : Type := arrow tags_t t t t.
    End P4Types.

    Arguments TBool {_}.
    Arguments TBit {_}.
    Arguments TInt {_}.
    Arguments TError {_}.
    Arguments TMatchKind {_}.
    Arguments TRecord {_}.
    Arguments THeader {_}.
    Arguments THeaderStack {_}.

    Module TypeNotations.
      Notation "'{{' ty '}}'" := ty (ty custom p4type at level 99).
      Notation "( x )" := x (in custom p4type, x at level 99).
      Notation "x" := x (in custom p4type at level 0, x constr at level 0).
      Notation "'Bool'" := TBool (in custom p4type at level 0).
      Notation "'bit' < w >"
        := (TBit w)
            (in custom p4type at level 2, no associativity).
      Notation "'int' < w >"
        := (TInt w)
            (in custom p4type at level 2, no associativity).
      Notation "'error'" := TError
                              (in custom p4type at level 0,
                                  no associativity).
      Notation "'matchkind'"
        := TMatchKind (in custom p4type at level 0, no associativity).
      Notation "'rec' { fields }"
        := (TRecord fields)
            (in custom p4type at level 6, no associativity).
      Notation "'hdr' { fields }"
        := (THeader fields)
            (in custom p4type at level 6, no associativity).
      Notation "'stack' fields [ n ]"
               := (THeaderStack fields n) (in custom p4type at level 7).
    End TypeNotations.

    (** Custom induction principle for [t]. *)
    Section TypeInduction.
      Context {tags_t : Type}.

      Import TypeNotations.

      (** An arbitrary property. *)
      Variable P : t tags_t -> Prop.

      Hypothesis HTBool : P {{ Bool }}.

      Hypothesis HTBit : forall w, P {{ bit<w> }}.

      Hypothesis HTInt : forall w, P {{ int<w> }}.

      Hypothesis HTError : P {{ error }}.

      Hypothesis HTMatchKind : P {{ matchkind }}.

      Hypothesis HTRecord : forall fields,
          F.predfs_data P fields -> P {{ rec { fields } }}.

      Hypothesis HTHeader : forall fields,
          F.predfs_data P fields -> P {{ hdr { fields } }}.

      Hypothesis HTHeaderStack : forall fields size,
          F.predfs_data P fields -> P {{ stack fields[size] }}.

      (** A custom induction principle.
          Do [induction ?t using custom_t_ind]. *)
      Definition custom_t_ind : forall ty : t tags_t, P ty :=
        fix custom_t_ind (type : t tags_t) : P type :=
          let fix fields_ind
                  (flds : F.fs tags_t (t tags_t)) : F.predfs_data P flds :=
              match flds as fs_ty return F.predfs_data P fs_ty with
              | [] => Forall_nil (F.predf_data P)
              | (_, hft) as hf :: tf =>
                Forall_cons hf (custom_t_ind hft) (fields_ind tf)
              end in
          match type as ty return P ty with
          | {{ Bool }} => HTBool
          | {{ bit<w> }} => HTBit w
          | {{ int<w> }} => HTInt w
          | {{ error }} => HTError
          | {{ matchkind }} => HTMatchKind
          | {{ rec { fields } }} => HTRecord fields (fields_ind fields)
          | {{ hdr { fields } }} => HTHeader fields (fields_ind fields)
          | {{ stack fields[n] }} => HTHeaderStack fields n (fields_ind fields)
          end.
      (**[]*)
    End TypeInduction.

    Module TypeEquivalence.
      Import Field.FieldTactics.

      Section TypeEquivalence.
        Context {tags_t : Type}.

        Import TypeNotations.

        (** Equality of types. *)
        Inductive equivt : t tags_t -> t tags_t -> Prop :=
        | equivt_bool : ∫ Bool ≡ Bool
        | equivt_bit (w : positive) : ∫ bit<w> ≡ bit<w>
        | equivt_int (w : positive) : ∫ int<w> ≡ int<w>
        | equivt_error : ∫ error ≡ error
        | equivt_matchkind : ∫ matchkind ≡ matchkind
        | equivt_record (fs1 fs2 : F.fs tags_t (t tags_t)) :
            F.relfs equivt fs1 fs2 ->
            ∫ rec { fs1 } ≡ rec { fs2 }
        | equivt_header (fs1 fs2 : F.fs tags_t (t tags_t)) :
            F.relfs equivt fs1 fs2 ->
            ∫ hdr { fs1 } ≡ hdr { fs2 }
        | equivt_stack (n : positive) (fs1 fs2 : F.fs tags_t (t tags_t)) :
            F.relfs equivt fs1 fs2 ->
            ∫ stack fs1[n] ≡ stack fs2[n]
        where "∫ t1 ≡ t2" := (equivt t1 t2).
        (**[]*)

        (** A custom induction principle for type equivalence. *)
        Section TypeEquivInduction.
          (** An arbitrary predicate. *)
          Variable P : t tags_t -> t tags_t -> Prop.

          Hypothesis HBool : P {{ Bool }} {{ Bool }}.

          Hypothesis HBit : forall w, P {{ bit<w> }} {{ bit<w> }}.

          Hypothesis HInt : forall w, P {{ int<w> }} {{ int<w> }}.

          Hypothesis HError : P {{ error }} {{ error }}.

          Hypothesis HMatchkind : P {{ matchkind }} {{ matchkind }}.

          Hypothesis HRecord : forall fs1 fs2,
              F.relfs equivt fs1 fs2 ->
              F.relfs P fs1 fs2 ->
              P {{ rec { fs1 } }} {{ rec { fs2 } }}.

          Hypothesis HHeader : forall fs1 fs2,
              F.relfs equivt fs1 fs2 ->
              F.relfs P fs1 fs2 ->
              P {{ hdr { fs1 } }} {{ hdr { fs2 } }}.

          Hypothesis HStack : forall n fs1 fs2,
              F.relfs equivt fs1 fs2 ->
              F.relfs P fs1 fs2 ->
              P {{ stack fs1[n] }} {{ stack fs2[n] }}.

          (** A custom induction principle for type equivalence.
              Do [induction ?H using custom_equivt_ind]. *)
          Definition custom_equivt_ind :
            forall (τ1 τ2 : t tags_t) (H : ∫ τ1 ≡ τ2), P τ1 τ2 :=
            fix cind t1 t2 H :=
              let fix find
                      {ts1 ts2 : F.fs tags_t (t tags_t)}
                      (HR : F.relfs equivt ts1 ts2) : F.relfs P ts1 ts2 :=
                  match HR in Forall2 _ t1s t2s return Forall2 (F.relf P) t1s t2s with
                  | Forall2_nil _ => Forall2_nil (F.relf P)
                  | Forall2_cons t1 t2
                                 (conj HName Hequivt)
                                 Htail => Forall2_cons
                                           t1 t2
                                           (conj
                                              HName
                                              (cind _ _ Hequivt))
                                           (find Htail)
                  end in
                      match H in ∫ τ1 ≡ τ2 return P τ1 τ2 with
                      | equivt_bool => HBool
                      | equivt_bit w => HBit w
                      | equivt_int w => HInt w
                      | equivt_error => HError
                      | equivt_matchkind => HMatchkind
                      | equivt_record _ _ Hequiv => HRecord _ _ Hequiv (find Hequiv)
                      | equivt_header _ _ Hequiv => HHeader _ _ Hequiv (find Hequiv)
                      | equivt_stack n _ _ HEquiv => HStack n _ _ HEquiv (find HEquiv)
                      end.
                  (**[]*)
        End TypeEquivInduction.

        Lemma equivt_reflexive : Reflexive equivt.
        Proof.
          intros ty;
            induction ty using custom_t_ind; constructor;
              try (induction H; constructor; auto;
                   destruct x as [x ty]; unfold F.relf; simpl in *;
                   split; auto; try reflexivity).
        Qed.

        Lemma equivt_symmetric : Symmetric equivt.
        Proof.
          unfold Symmetric; intros t1 t2 H;
            induction H using custom_equivt_ind;
            constructor; auto;
              try (induction H; inversion H0; subst; repeat constructor; auto;
                   destruct x as [x1 t1]; destruct y as [x2 t2];
                   repeat match goal with
                          | H: F.relf _ _ _ |- _ => inversion H; subst; clear H
                          end; simpl in *; auto;
                   [ symmetry | apply IHForall2 ]; auto).
        Qed.

        Lemma equivt_transitive : Transitive equivt.
        Proof.
          intros x; induction x using custom_t_ind;
            intros [] [] Hxy Hyz; auto;
              inversion Hxy; inversion Hyz; subst; auto; clear Hxy Hyz;
                try (rename fields into fs1; rename fields0 into fs2;
                     rename fields1 into fs3; constructor;
                     generalize dependent fs3; generalize dependent fs2;
                     induction fs1 as [| [x1 t1] fs1 IHfs1];
                     intros [| [x2 t2] fs2] H12; intros [| [x3 t3] fs3] H23;
                     inversion H12; inversion H23; inversion H;
                     clear H12 H23 H; subst; constructor;
                     [ unfold F.relf in *; simpl in *;
                       destruct H3; destruct H9; split; eauto;
                       transitivity x2; assumption
                     | eapply IHfs1; eauto]).
        Qed.

        Instance TypeEquivalence : Equivalence equivt.
        Proof.
          constructor; [ apply equivt_reflexive
                       | apply equivt_symmetric
                       | apply equivt_transitive].
        Defined.

        Lemma equivt_dec : forall (t1 t2 : t tags_t),
            equivt t1 t2 \/ ~ equivt t1 t2.
        Proof.
          induction t1 using custom_t_ind; intros [];
            try (left; apply equivt_reflexive);
            try (right; intros HR; inversion HR; assumption);
            try (destruct (equiv_dec w width) as [Hwidth | Hwidth];
                 unfold equiv in *; unfold complement in *; subst;
                 try (right; intros H'; inversion H'; contradiction);
                 try (left; reflexivity));
            try (destruct (equiv_dec size size0) as [Hsize | Hsize];
                 unfold equiv in *; unfold complement in *; subst;
                 try (right; intros H'; inversion H'; contradiction));
            try (rename fields into fs1; rename fields0 into fs2;
                 generalize dependent fs2;
                 induction fs1 as [| [x1 t1] fs1 IHfs1];
                 intros [| [x2 t2] fs2];
                 try (left; reflexivity);
                 try (right; intros H';
                      inversion H'; try invert_nil_cons_relate; assumption); subst;
                 inversion H; clear H; subst; unfold F.predf_data in *;
                 pose proof IHfs1 H3 fs2 as IH; clear IHfs1 H3;
                 destruct (equiv_dec x1 x2) as [H12 | H12];
                 unfold equiv in *; unfold complement in *;
                 destruct (H2 t2) as [HT | HT]; clear H2;
                 destruct IH as [IH | IH];
                 try (right; intros H'; inversion H';
                      clear H'; subst; invert_cons_cons_relate;
                      subst; unfold F.relf in *;
                      simpl in *; destruct H3; contradiction);
                 [ left; constructor; inversion IH; subst;
                   constructor; auto; unfold F.relf; split; auto
                 | right; intros H'; inversion H'; subst;
                   clear H'; invert_cons_cons_relate; subst; apply IH;
                   constructor; auto ]).
        Qed.
      End TypeEquivalence.
    End TypeEquivalence.

    Inductive uop : Set :=
    | Not    (* boolean negation *)
    | BitNot (* bitwise negation *)
    | UMinus (* integer negation *).
    (**[]*)

    Module UopNotations.
      Notation "x" := x (in custom p4uop at level 0, x constr at level 0).
      Notation "!" := Not (in custom p4uop at level 0).
      Notation "~" := BitNot (in custom p4uop at level 0).
      Notation "-" := UMinus (in custom p4uop at level 0).
    End UopNotations.

    (** Binary operations.
        The "Sat" suffix denotes
        saturating arithmetic:
        where there is no overflow. *)
    Inductive bop : Set :=
    | Plus     (* integer addition *)
    | PlusSat  (* saturating addition *)
    | Minus    (* integer subtraction *)
    | MinusSat (* saturating subtraction *)
    | Shl      (* bitwise left-shift *)
    | Shr      (* bitwise right-shift *)
    | Le       (* integer less-than *)
    | Ge       (* integer greater-than *)
    | Lt       (* integer less-than or equals *)
    | Gt       (* integer greater-than or equals *)
    | Eq       (* expression equality *)
    | NotEq    (* expression inequality *)
    | BitAnd   (* bitwise and *)
    | BitXor   (* bitwise exclusive-or *)
    | BitOr    (* bitwise or *)
    | PlusPlus (* bit-string concatenation *)
    | And      (* boolean and *)
    | Or       (* boolean or *).
    (**[]*)

    Module BopNotations.
      Notation "x" := x (in custom p4bop at level 0, x constr at level 0).
      Notation "+" := Plus (in custom p4bop at level 0).
      Notation "-" := Minus (in custom p4bop at level 0).
      Notation "'|+|'" := PlusSat (in custom p4bop at level 0).
      Notation "'|-|'" := MinusSat (in custom p4bop at level 0).
      Notation "'<<'" := Shl (in custom p4bop at level 0).
      Notation "'>>'" := Shr (in custom p4bop at level 0).
      Notation "'<='" := Le (in custom p4bop at level 0).
      Notation "'>='" := Ge (in custom p4bop at level 0).
      Notation "<" := Lt (in custom p4bop at level 0).
      Notation ">" := Gt (in custom p4bop at level 0).
      Notation "'=='" := Eq (in custom p4bop at level 0).
      Notation "'!='" := NotEq (in custom p4bop at level 0).
      Notation "&" := BitAnd (in custom p4bop at level 0).
      Notation "^" := BitXor (in custom p4bop at level 0).
      Notation "|" := BitOr (in custom p4bop at level 0).
      Notation "'&&'" := And (in custom p4bop at level 0).
      Notation "'||'" := Or (in custom p4bop at level 0).
      Notation "'++'" := PlusPlus (in custom p4bop at level 0).
    End BopNotations.

    (** Default matchkinds. *)
    Inductive matchkind : Set :=
    | MKExact
    | MKTernary
    | MKLpm.
    (**[]*)

    Instance MatchKindEqDec : EqDec matchkind eq.
    Proof.
      unfold EqDec; unfold equiv, complement.
      intros [] []; try (left; reflexivity);
        try (right; intros H; inversion H).
    Defined.

    Module MatchkindNotations.
      Notation "x" := x (in custom p4matchkind at level 0, x constr at level 0).
      Notation "'exact'" := MKExact (in custom p4matchkind at level 0).
      Notation "'ternary'" := MKTernary (in custom p4matchkind at level 0).
      Notation "'lpm'" := MKLpm (in custom p4matchkind at level 0).
    End MatchkindNotations.

    (** Header operations. *)
    Inductive hdr_op : Set :=
    | HOIsValid
    | HOSetValid
    | HOSetInValid.
    (**[]*)

    Module HeaderOpNotations.
      Notation "x" := x (in custom p4hdr_op at level 0, x constr at level 0).
      Notation "'isValid'" := HOIsValid (in custom p4hdr_op at level 0).
      Notation "'setValid'" := HOSetValid (in custom p4hdr_op at level 0).
      Notation "'setInValid'" := HOSetInValid (in custom p4hdr_op at level 0).
    End HeaderOpNotations.

    Section Expressions.
      Variable (tags_t : Type).

      (** Expressions annotated with types,
          unless the type is obvious. *)
      Inductive e : Type :=
      | EBool (b : bool) (i : tags_t)                      (* booleans *)
      | EBit (width : positive) (val : N) (i : tags_t)  (* unsigned integers *)
      | EInt (width : positive) (val : Z) (i : tags_t)  (* signed integers *)
      | EVar (type : t tags_t) (x : name tags_t)
             (i : tags_t)                               (* variables *)
      | EUop (op : uop) (type : t tags_t)
             (arg : e) (i : tags_t)                     (* unary operations *)
      | EBop (op : bop) (lhs_type rhs_type : t tags_t)
             (lhs rhs : e) (i : tags_t)                 (* binary operations *)
      | ERecord (fields : F.fs tags_t (t tags_t * e))
                (i : tags_t)                           (* records and structs *)
      | EHeader (fields : F.fs tags_t (t tags_t * e))
                (valid : e) (i : tags_t)               (* header literals *)
      | EHeaderOp (op : hdr_op) (header : e)
                  (i : tags_t)                         (* header operations *)
      | EExprMember (mem : string tags_t)
                    (expr_type : t tags_t)
                    (arg : e) (i : tags_t)             (* member-expressions *)
      | EError (err : option (string tags_t))
               (i : tags_t)                            (* error literals *)
      | EMatchKind (mk : matchkind) (i : tags_t)       (* matchkind literals *)
      | EHeaderStack (fields : F.fs tags_t (t tags_t))
                     (headers : list e) (size : positive)
                     (next_index : N)                  (* header stack literals,
                                                          unique to p4light *)
      | EHeaderStackAccess (stack : e) (index : N)
                           (i : tags_t)                (* header stack indexing *).
      (**[]*)

      (** Function call arguments. *)
      Definition args : Type :=
        F.fs tags_t (paramarg (t tags_t * e) (t tags_t * e)).
      (**[]*)

      (** Function call. *)
      Definition arrowE : Type :=
        arrow tags_t (t tags_t * e) (t tags_t * e) (t tags_t * e).
      (**[]*)
    End Expressions.

    Arguments EBool {tags_t}.
    Arguments EBit {_}.
    Arguments EInt {_}.
    Arguments EVar {tags_t}.
    Arguments EUop {tags_t}.
    Arguments EBop {tags_t}.
    Arguments ERecord {tags_t}.
    Arguments EHeader {_}.
    Arguments EHeaderOp {_}.
    Arguments EExprMember {tags_t}.
    Arguments EError {tags_t}.
    Arguments EMatchKind {tags_t}.
    Arguments EHeaderStack {_}.
    Arguments EHeaderStackAccess {_}.

    Module ExprNotations.
      Export UopNotations.
      Export BopNotations.
      Export MatchkindNotations.
      Export HeaderOpNotations.
      Export TypeNotations.

      Notation "'<{' exp '}>'" := exp (exp custom p4expr at level 99).
      Notation "( x )" := x (in custom p4expr, x at level 99).
      Notation "x" := x (in custom p4expr at level 0, x constr at level 0).
      Notation "'True' @ i" := (EBool true i) (in custom p4expr at level 0).
      Notation "'False' @ i" := (EBool false i) (in custom p4expr at level 0).
      Notation "'BOOL' b @ i" := (EBool b i) (in custom p4expr at level 0).
      Notation "w 'W' n @ i" := (EBit w n i) (in custom p4expr at level 0).
      Notation "w 'S' n @ i" := (EInt w n i) (in custom p4expr at level 0).
      Notation "'Var' x : ty @ i" := (EVar ty x i)
                            (in custom p4expr at level 0, no associativity).
      Notation "'UOP' op x : ty @ i"
               := (EUop op ty x i)
                    (in custom p4expr at level 2,
                        x custom p4expr, ty custom p4type,
                        op custom p4uop, no associativity).
      Notation "'BOP' x : tx op y : ty @ i"
               := (EBop op tx ty x y i)
                    (in custom p4expr at level 10,
                        x custom p4expr, tx custom p4type,
                        y custom p4expr, ty custom p4type,
                        op custom p4bop, left associativity).
      Notation "'rec' { fields } @ i "
        := (ERecord fields i)
            (in custom p4expr at level 6, no associativity).
      Notation "'hdr' { fields } 'valid' ':=' b @ i "
        := (EHeader fields b i)
            (in custom p4expr at level 6,
                b custom p4expr, no associativity).
      Notation "'H' op exp @ i"
               := (EHeaderOp op exp i)
                    (in custom p4expr at level 5, exp custom p4expr,
                        op custom p4hdr_op, no associativity).
      Notation "'Mem' x : ty 'dot' y @ i"
              := (EExprMember y ty x i)
                    (in custom p4expr at level 10, x custom p4expr,
                        ty custom p4type, left associativity).
      Notation "'Error' x @ i" := (EError x i)
                              (in custom p4expr at level 0, no associativity).
      Notation "'Matchkind' mk @ i" := (EMatchKind mk i)
                              (in custom p4expr at level 0,
                                  mk custom p4matchkind, no associativity).
      Notation "'Stack' hdrs : ts [ n ] 'nextIndex' ':=' ni"
               := (EHeaderStack ts hdrs n ni)
                    (in custom p4expr at level 0).
      Notation "'Access' e1 [ e2 ] @ i"
               := (EHeaderStackAccess e1 e2 i)
                    (in custom p4expr at level 10, e1 custom p4expr).
    End ExprNotations.

    (** A custom induction principle for [e]. *)
    Section ExprInduction.
      Import ExprNotations.

      (** An arbitrary predicate. *)
      Context {tags_t : Type}.

      Variable P : e tags_t -> Prop.

      Hypothesis HEBool : forall b i, P <{ BOOL b @ i }>.

      Hypothesis HEBit : forall w n i, P <{ w W n @ i }>.

      Hypothesis HEInt : forall w n i, P <{ w S n @ i }>.

      Hypothesis HEVar : forall (ty : t tags_t) (x : name tags_t) i,
          P <{ Var x : ty @ i }>.

      Hypothesis HEUop : forall (op : uop) (ty : t tags_t) (ex : e tags_t) i,
          P ex -> P <{ UOP op ex : ty @ i }>.

      Hypothesis HEBop : forall (op : bop) (lt rt : t tags_t) (lhs rhs : e tags_t) i,
          P lhs -> P rhs -> P <{ BOP lhs:lt op rhs:rt @ i }>.

      Hypothesis HERecord : forall (fields : F.fs tags_t (t tags_t * e tags_t)) i,
          F.predfs_data (P ∘ snd) fields -> P <{ rec {fields} @ i }>.

      Hypothesis HEHeader : forall (fields : F.fs tags_t (t tags_t * e tags_t)) b i,
          F.predfs_data (P ∘ snd) fields -> P <{ hdr {fields} valid:=b @ i }>.

      Hypothesis HEHeaderOp : forall op exp i,
          P exp -> P <{ H op exp @ i }>.

      Hypothesis HEExprMember : forall (x : string tags_t)
                                  (ty : t tags_t) (ex : e tags_t) i,
          P ex -> P <{ Mem ex:ty dot x @ i }>.

      Hypothesis HEError : forall err i, P <{ Error err @ i }>.

      Hypothesis HEMatchKind : forall mkd i, P <{ Matchkind mkd @ i }>.

      Hypothesis HEStack : forall ts hs size ni,
          Forall P hs ->
          P <{ Stack hs:ts [size] nextIndex:=ni }>.

      Hypothesis HAccess : forall e1 e2 i,
          P e1 -> P <{ Access e1[e2] @ i }>.

      (** A custom induction principle.
          Do [induction ?e using custom_e_ind]. *)
      Definition custom_e_ind : forall exp : e tags_t, P exp :=
        fix eind (expr : e tags_t) : P expr :=
          let fix fields_ind {A:Type} (flds : F.fs tags_t (A * e tags_t))
              : F.predfs_data (P ∘ snd) flds :=
              match flds as fs_ex
                    return F.predfs_data (P ∘ snd) fs_ex with
              | [] => Forall_nil (F.predf_data (P ∘ snd))
              | (_, (_, hfe)) as hf :: tf =>
                Forall_cons hf (eind hfe) (fields_ind tf)
              end in
          let fix list_ind (es : list (e tags_t)) : Forall P es :=
              match es as ees return Forall P ees with
              | [] => Forall_nil P
              | exp :: ees => Forall_cons exp (eind exp) (list_ind ees)
              end in
          match expr as e' return P e' with
          | <{ BOOL b @ i }> => HEBool b i
          | <{ w W n @ i }>  => HEBit w n i
          | <{ w S n @ i }>  => HEInt w n i
          | <{ Var x:ty @ i }> => HEVar ty x i
          | <{ UOP op exp:ty @ i }> => HEUop op ty exp i (eind exp)
          | <{ BOP lhs:lt op rhs:rt @ i }> =>
              HEBop op lt rt lhs rhs i
                    (eind lhs) (eind rhs)
          | <{ rec { fields } @ i }> => HERecord fields i (fields_ind fields)
          | <{ hdr { fields } valid:=b @ i }> => HEHeader fields b i (fields_ind fields)
          | <{ H op exp @ i }> => HEHeaderOp op exp i (eind exp)
          | <{ Mem exp:ty dot x @ i }> =>
              HEExprMember x ty exp i (eind exp)
          | <{ Error err @ i }> => HEError err i
          | <{ Matchkind mkd @ i }> => HEMatchKind mkd i
          | <{ Stack hs:ts [n] nextIndex:=ni }> => HEStack ts hs n ni (list_ind hs)
          | <{ Access e1[e2] @ i }> => HAccess e1 e2 i (eind e1)
          end.
      (**[]*)
    End ExprInduction.
  End Expr.

  (** * Statement Grammar *)
  Module Stmt.
    Import Dir.
    Module E := Expr.

    Section Statements.
      Variable (tags_t : Type).

      Inductive s : Type :=
      | SSkip (i : tags_t)                              (* skip, useful for
                                                           small-step semantics *)
      | SVardecl (type : E.t tags_t)
                 (x : string tags_t) (i : tags_t)       (* Variable declaration. *)
      | SAssign (type : E.t tags_t) (lhs rhs : E.e tags_t)
                (i : tags_t)                            (* assignment *)
      | SConditional (guard_type : E.t tags_t)
                     (guard : E.e tags_t)
                     (tru_blk fls_blk : s) (i : tags_t) (* conditionals *)
      | SSeq (s1 s2 : s) (i : tags_t)                   (* sequences,
                                                           an alternative to blocks *)
      | SFunCall (f : name tags_t)
                 (args : E.arrowE tags_t) (i : tags_t)  (* function call *)
      | SActCall (f : name tags_t)
                 (args : E.args tags_t) (i : tags_t)    (* action call *)
      | SReturnVoid (i : tags_t)                        (* void return statement *)
      | SReturnFruit (t : E.t tags_t)
                     (e : E.e tags_t)(i : tags_t)       (* fruitful return statement *)
      | SExit (i : tags_t)                              (* exit statement *)
      | SInvoke (x : name tags_t) (i : tags_t)          (* table invocation *)
      | SApply (x : name tags_t)
               (args : E.args tags_t) (i : tags_t)      (* control apply statements,
                                                           where [x] is the
                                                           name of an instance *).
    (**[]*)
    End Statements.

    Arguments SSkip {tags_t}.
    Arguments SVardecl {_}.
    Arguments SAssign {tags_t}.
    Arguments SConditional {tags_t}.
    Arguments SSeq {tags_t}.
    Arguments SFunCall {_}.
    Arguments SActCall {_}.
    Arguments SReturnVoid {tags_t}.
    Arguments SReturnFruit {tags_t}.
    Arguments SExit {_}.
    Arguments SApply {_}.
    Arguments SInvoke {_}.

    Module StmtNotations.
      Export E.ExprNotations.

      Notation "'-{' stmt '}-'" := stmt (stmt custom p4stmt at level 99).
      Notation "( x )" := x (in custom p4stmt, x at level 99).
      Notation "x"
        := x (in custom p4stmt at level 0, x constr at level 0).
      Notation "'skip' @ i" := (SSkip i) (in custom p4stmt at level 0).
      Notation "s1 ; s2 @ i"
        := (SSeq s1 s2 i) (in custom p4stmt at level 99,
                            s1 custom p4stmt, s2 custom p4stmt,
                            right associativity).
      Notation "'var' x : t @ i"
               := (SVardecl t x i)
                    (in custom p4stmt at level 0, t custom p4type).
      Notation "'asgn' e1 ':=' e2 : t @ i"
              := (SAssign t e1 e2 i)
                    (in custom p4stmt at level 40,
                        e1 custom p4expr, e2 custom p4expr,
                        t custom p4type, no associativity).
      Notation "'if' e : t 'then' s1 'else' s2 @ i"
              := (SConditional t e s1 s2 i)
                    (in custom p4stmt at level 80,
                        t custom p4type, e custom p4expr,
                        s1 custom p4stmt, s2 custom p4stmt,
                        no associativity).
      Notation "'call' f 'with' args @ i"
        := (SFunCall f (Arrow args None) i)
             (in custom p4stmt at level 30, no associativity).
      Notation "'let' e : t ':=' 'call' f 'with' args @ i"
               := (SFunCall f (Arrow args (Some (t,e))) i)
                    (in custom p4stmt at level 30,
                        e custom p4expr, t custom p4stmt, no associativity).
      Notation "'calling' a 'with' args @ i"
               := (SActCall a args i) (in custom p4stmt at level 3).
      Notation "'return' e : t @ i"
               := (SReturnFruit t e i)
                    (in custom p4stmt at level 30,
                        e custom p4expr, t custom p4type, no associativity).
      Notation "'returns' @ i"
               := (SReturnVoid i)
                    (in custom p4stmt at level 0, no associativity).
      Notation "'exit' @ i"
               := (SExit i) (in custom p4stmt at level 0, no associativity).
      Notation "'apply' x 'with' args @ i"
               := (SApply x args i) (in custom p4stmt at level 0, no associativity).
      Notation "'invoke' tbl @ i"
               := (SInvoke tbl i) (in custom p4stmt at level 0).
    End StmtNotations.
  End Stmt.

  (** * Declaration Grammar *)
  Module Decl.
    Module E := Expr.
    Module S := Stmt.

    Section Declarations.
      Variable (tags_t : Type).

      (** Here is the subset of declarations that
          may occur within controls, parsers,
          and even the top-level. *)
      Inductive d : Type :=
      | DVardecl (typ : E.t tags_t) (x : string tags_t)
                 (i : tags_t)                      (* unitialized variable *)
      | DVarinit (typ : E.t tags_t) (x : string tags_t)
                 (rhs : E.e tags_t) (i : tags_t)   (* initialized variable *)
      | DInstantiate (C : name tags_t) (x : string tags_t)
                     (args : F.fs tags_t (E.t tags_t * E.e tags_t))
                     (i : tags_t)                  (* constructor [C]
                                                      with [args] makes [x] *)
      | DSeq (d1 d2 : d) (i : tags_t)              (* sequence of declarations *).
    (**[]*)
    End Declarations.

    Arguments DVardecl {tags_t}.
    Arguments DVarinit {tags_t}.
    Arguments DInstantiate {tags_t}.
    Arguments DSeq {tags_t}.

    Module DeclNotations.
      Export S.StmtNotations.

      Notation "';{' decl '};'" := decl (decl custom p4decl at level 99).
      Notation "( x )" := x (in custom p4decl, x at level 99).
      Notation "x"
        := x (in custom p4decl at level 0, x constr at level 0).
      Notation "'Var' x : t @ i"
        := (DVardecl t x i) (in custom p4decl at level 0, t custom p4type).
      Notation "'Let' x : t ':=' e @ i"
        := (DVarinit t x e i)
             (in custom p4decl at level 0, t custom p4type, e custom p4expr).
      Notation "'Instance' x 'of' c ( args ) @ i"
               := (DInstantiate c x args i) (in custom p4decl at level 0).
      Notation "d1 ';;' d2 @ i"
               := (DSeq d1 d2 i)
                    (in custom p4decl at level 10,
                        d1 custom p4decl, d2 custom p4decl,
                        right associativity).
    End DeclNotations.
  End Decl.

  (** * Controls *)
  Module Control.
    Module E := Expr.
    Module S := Stmt.
    Module D := Decl.

    Module ControlDecl.
      Section ControlDecls.
        Variable (tags_t : Type).

        (** Table. *)
        Inductive table : Type :=
        | Table (key : list (E.t tags_t * E.e tags_t * E.matchkind))
                (actions : list (string tags_t)).
        (**[]*)

        (** Declarations that may occur within Controls. *)
        (* TODO, this is a stub. *)
        Inductive d : Type :=
        | CDAction (a : string tags_t)
                   (signature : E.params tags_t)
                   (body : S.s tags_t) (i : tags_t) (* action declaration *)
        | CDTable (t : string tags_t) (bdy : table)
                  (i : tags_t)                      (* table declaration *)
        | CDDecl (d : D.d tags_t) (i : tags_t)
        | CDSeq (d1 d2 : d) (i : tags_t).
        (**[]*)
      End ControlDecls.

      Arguments Table {_}.
      Arguments CDAction {_}.
      Arguments CDTable {_}.
      Arguments CDDecl {_}.
      Arguments CDSeq {_}.

      Module ControlDeclNotations.
        Export D.DeclNotations.

        Notation "'c{' decl '}c'" := decl (decl custom p4ctrldecl at level 99).
        Notation "( x )" := x (in custom p4ctrldecl, x at level 99).
        Notation "x"
          := x (in custom p4ctrldecl at level 0, x constr at level 0).
        Notation "d1 ';c;' d2 @ i"
          := (CDSeq d1 d2 i)
               (in custom p4ctrldecl at level 10,
                   d1 custom p4ctrldecl, d2 custom p4ctrldecl,
                   right associativity).
        Notation "'Decl' d @ i"
          := (CDDecl d i)
               (in custom p4ctrldecl at level 0, d custom p4decl).
        Notation "'action' a ( params ) { body } @ i"
          := (CDAction a params body i)
               (in custom p4ctrldecl at level 0, body custom p4stmt).
        Notation "'table' t 'key' ':=' ems 'actions' ':=' acts @ i"
          := (CDTable t (Table ems acts) i)
               (in custom p4ctrldecl at level 0).
      End ControlDeclNotations.
    End ControlDecl.
  End Control.

  (** * Top-Level Declarations *)
  Module TopDecl.
    Module E := Expr.
    Module S := Stmt.
    Module D := Decl.
    Module C := Control.ControlDecl.

    Section TopDeclarations.
      Variable (tags_t : Type).

      (** Top-level declarations. *)
      (* TODO, this is a stub. *)
      Inductive d : Type :=
      | TPDecl (d : D.d tags_t) (i : tags_t)
      | TPControl (c : string tags_t)
                  (cparams : F.fs tags_t (E.t tags_t)) (* constructor params *)
                  (params : E.params tags_t) (* apply block params *)
                  (body : C.d tags_t) (apply_blk : S.s tags_t) (i : tags_t)
      | TPParser (p : string tags_t)
                 (cparams : F.fs tags_t (E.t tags_t)) (* constructor params *)
                 (params : E.params tags_t) (* invocation params *)
                 (i : tags_t) (* TODO! *)
      | TPFunction (f : string tags_t) (signature : E.arrowT tags_t)
                   (body : S.s tags_t) (i : tags_t)
                   (* function/method declaration *)
      | TPSeq (d1 d2 : d) (i : tags_t).
      (**[]*)
    End TopDeclarations.

    Arguments TPDecl {_}.
    Arguments TPControl {_}.
    Arguments TPParser {_}.
    Arguments TPFunction {_}.
    Arguments TPSeq {_}.

    Module TopDeclNotations.
      Export C.ControlDeclNotations.

      Notation "'%{' decl '}%'" := decl (decl custom p4topdecl at level 99).
      Notation "( x )" := x (in custom p4topdecl, x at level 99).
      Notation "x"
        := x (in custom p4topdecl at level 0, x constr at level 0).
      Notation "d1 ';%;' d2 @ i"
               := (TPSeq d1 d2 i)
                    (in custom p4topdecl at level 10,
                        d1 custom p4topdecl, d2 custom p4topdecl,
                        right associativity).
      Notation "'DECL' d @ i"
        := (TPDecl d i)
             (in custom p4topdecl at level 0, d custom p4decl).
      Notation "'void' f ( params ) { body } @ i"
               := (TPFunction f (Arrow params None) body i)
                    (in custom p4topdecl at level 0, body custom p4stmt).
      Notation "'fn' f ( params ) '->' t { body } @ i"
               := (TPFunction f (Arrow params (Some t)) body i)
                    (in custom p4topdecl at level 0,
                        t custom p4type, body custom p4stmt).
      Notation "'control' c ( cparams ) ( params ) 'apply' { blk } 'where' { body } @ i"
               := (TPControl c cparams params body blk i)
                    (in custom p4topdecl at level 0,
                        blk custom p4stmt, body custom p4ctrldecl).
    End TopDeclNotations.
  End TopDecl.
End P4light.
