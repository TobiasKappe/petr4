Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bvector.

Require Import Info.
Require Import Typed.
Require String.

Section Syntax.

  Context (tags_t: Type).

  Inductive P4String :=
  | MkP4String (tags: tags_t) (s: String.t).

  Inductive P4Int :=
  | MkP4Int (tags: tags_t) (value: Z) (width_signed: option (nat * bool)).

  Inductive MethodPrototype :=
  | ProtoConstructor (tags: tags_t) (name: P4String)
                     (params: list P4Parameter)
  | ProtoAbstractMethod (tags: tags_t) (ret: P4Type)
                        (name: P4String)(type_params: list P4String)
                        (params: list P4Parameter)
  | ProtoMethod (tags: tags_t) (ret: P4Type)
                (name: P4String) (type_params: list P4String)
                (params: list P4Parameter).

  Inductive OpUni : Type :=
  | Not
  | BitNot
  | UMinus.

  Inductive OpBin : Type :=
  | Plus
  | PlusSat
  | Minus
  | MinusSat
  | Mul
  | Div
  | Mod
  | Shl
  | Shr
  | Le
  | Ge
  | Lt
  | Gt
  | Eq
  | NotEq
  | BitAnd
  | BitXor
  | BitOr
  | PlusPlus
  | And
  | Or.

  Inductive KeyValue :=
  | MkKeyValue (tags: tags_t) (key: P4String) (value: Expression)
  with ExpressionPreT :=
  | ExpBool (b: bool)
  | ExpInt (_: P4Int)
  | ExpString (_: P4String)
  | ExpName (_: Typed.name)
  | ExpArrayAccess (array: Expression) (index: Expression)
  | ExpBitStringAccess (bits: Expression) (lo: Expression) (hi: Expression)
  | ExpList (value: list Expression)
  | ExpRecord (entries: list KeyValue)
  | ExpUnaryOp (op: OpUni) (arg: Expression)
  | ExpBinaryOp (op: OpBin) (args: (Expression * Expression))
  | ExpCast (typ: P4Type) (expr: Expression)
  | ExpTypeMember (typ: Typed.name) (name: P4String)
  | ExpErrorMember (_: P4String)
  | ExpExpressionMember (expr: Expression) (name: P4String)
  | ExpTernary (cond: Expression) (tru: Expression) (fls: Expression)
  | ExpFunctionCall (func: Expression) (type_args: list P4Type)
                    (args: list (option Expression))
  | ExpNamelessInstantiation (typ: P4Type) (args: list Expression)
  | ExpDontCare
  | ExpMask (expr: Expression) (mask: Expression)
  | ExpRange (lo: Expression) (hi: Expression)
  with Expression :=
  | MkExpression (tags: tags_t) (expr: ExpressionPreT) (typ: P4Type) (dir: direction).

  Inductive MatchPreT :=
  | MatchDontCare
  | MatchExpression (expr: Expression).
  Inductive Match :=
  | MkMatch (tags: tags_t) (expr: MatchPreT) (typ: P4Type).

  Inductive TablePreActionRef :=
  | MkTablePreActionRef (name: Typed.name)
                        (args: list (option Expression)).
  Inductive TableActionRef :=
  | MkTableActionRef (tags: tags_t) (action: TablePreActionRef)
                     (typ: Typed.P4Type).

  Inductive TableKey :=
  | MkTableKey (tags: tags_t)  (key: list Expression)
               (match_kind: P4String).

  Inductive TableEntry :=
  | MkTableEntry (tags: tags_t)  (matches: list Match)
                 (action: TableActionRef).

  Inductive TableProperty :=
  | MkTableProperty (tags: tags_t)  (const: bool)
                    (name: P4String) (value: Expression).

  Inductive ValueBase :=
  | ValBaseNull
  | ValBaseBool (_: bool)
  | ValBaseInteger (_: Z)
  | ValBaseBit (width: nat) (value: Bvector width)
  | ValBaseInt (width: nat) (value: Bvector width)
  | ValBaseVarbit (max: nat) (width: nat) (value: Bvector width)
  | ValBaseString (_: String.t)
  | ValBaseTuple (_: list ValueBase)
  | ValBaseRecord (_: list (String.t * ValueBase))
  | ValBaseSet (_: ValueSet)
  | ValBaseError (_: String.t)
  | ValBaseMatchKind (_: String.t)
  | ValBaseStruct (fields: list (String.t * ValueBase))
  | ValBaseHeader (fields: list (String.t * ValueBase)) (is_valid: bool)
  | ValBaseUnion (fields: list (String.t * ValueBase))
  | ValBaseStack (headers: list ValueBase) (size: nat) (next: nat)
  | ValBaseEnumField (typ_name: String.t) (enum_name: String.t)
  | ValBaseSenumField (typ_name: String.t) (enum_name: String.t) (value: ValueBase)
  | ValBaseSenum (_: list (String.t * ValueBase))
  with ValueSet :=
  | ValSetSingleton (width: nat) (value: Z)
  | ValSetUniversal
  | ValSetMask (value: ValueBase) (mask: ValueBase)
  | ValSetRange (lo: ValueBase) (hi: ValueBase)
  | ValSetProd (_: list ValueSet)
  | ValSetLpm (width: ValueBase) (nbits: nat) (value: ValueBase)
  | ValSetValueSet (size: ValueBase) (members: list (list Match))
                   (sets: list ValueSet).

  Inductive StatementSwitchLabel :=
  | StatSwLabDefault (tags: tags_t)
  | StatSwLabName (tags: tags_t) (_: P4String).

  Inductive StatementSwitchCase :=
  | StatSwCaseAction (tags: tags_t) (label: StatementSwitchLabel)
                     (code: list Statement)
  | StatSwCaseFallThrough (tags: tags_t) (label: StatementSwitchLabel)
  with StatementPreT :=
  | StatMethodCall (func: Expression) (type_args: list P4Type)
                   (args: list (option Expression))
  | StatAssignment (lhs: Expression) (rhs: Expression)
  | StatDirectApplication (typ: P4Type) (args: list Expression)
  | StatConditional (cond: Expression) (tru: Statement) (fls: option Statement)
  | StatBlock (statements: list Statement)
  | StatExit
  | StatEmpty
  | StatReturn (expr: option Expression)
  | StatSwitch (expr: Expression) (cases: list StatementSwitchCase)
  | StatConstant  (typ: P4Type)
                 (name: P4String) (value: ValueBase)
  | StatVariable  (typ: P4Type)
                 (name: P4String) (init: option Expression)
  | StatInstantiation  (typ: P4Type) (args: list Expression) (name: P4String)
                       (init: option (list Statement))
  with Statement :=
  | MkStatement (tags: tags_t) (stmt: StatementPreT) (typ: StmType).


  Section statement_mut_ind.

    Variables
        (P: Statement -> Prop)
        (P0: StatementPreT -> Prop)
        (P1: list Statement -> Prop)
        (P2: StatementSwitchCase -> Prop)
        (P3: list StatementSwitchCase -> Prop)
    .

    Hypotheses
        (H0: forall (tags : tags_t) (stmt : StatementPreT),
               P0 stmt -> forall typ : StmType, P (MkStatement tags stmt typ))
        (H1: forall (func : Expression)
                    (type_args : list P4Type)
                    (args : list (option Expression)),
               P0 (StatMethodCall func type_args args))
        (H2: forall lhs rhs : Expression, P0 (StatAssignment lhs rhs))
        (H3: forall (typ : P4Type) (args : list Expression),
               P0 (StatDirectApplication typ args))
        (H4: forall (cond : Expression) (tru : Statement),
               P tru -> P0 (StatConditional cond tru None))
        (H5: forall (cond : Expression) (tru : Statement) (fls: Statement),
               P tru -> P fls -> P0 (StatConditional cond tru (Some fls)))
        (H6: forall block : list Statement,
               P1 block -> P0 (StatBlock block))
        (H7: P0 StatExit)
        (H8: P0 StatEmpty)
        (H9: forall expr : option Expression,
               P0 (StatReturn expr))
        (H10: forall (expr : Expression)
                     (cases : list StatementSwitchCase),
                P3 cases -> P0 (StatSwitch expr cases))
        (H11: forall (typ : P4Type)
                     (name : P4String)
                     (value : ValueBase),
              P0 (StatConstant typ name value))
        (H12: forall (typ : P4Type)
                     (name : P4String)
                     (init : option Expression),
                P0 (StatVariable typ name init))
        (H13: forall (typ : P4Type)
                     (args : list Expression)
                     (name : P4String)
                     (init : option (list Statement)),
                P0 (StatInstantiation typ args name init))
        (H14: P1 nil)
        (H15: forall (statement : Statement),
                P statement ->
                forall (rest : list Statement),
                  P1 rest -> P1 (statement :: rest)%list)
        (H16: P3 nil)
        (H17: forall (case: StatementSwitchCase),
                P2 case ->
                forall (rest: list StatementSwitchCase),
                  P3 rest -> P3 (case :: rest)%list)
        (H18: forall (tags: tags_t)
                     (label: StatementSwitchLabel)
                     (code: list Statement),
                P1 code -> P2 (StatSwCaseAction tags label code))
        (H19: forall (tags: tags_t) (label: StatementSwitchLabel),
                P2 (StatSwCaseFallThrough tags label))
    .

    Fixpoint statement_mut (stmt: Statement): P stmt
    :=
      let statement_mut_block :=
        fix f (block: list Statement) : P1 block :=
          match block with
          | nil => H14
          | cons stmt_first block' =>
            H15 stmt_first (statement_mut stmt_first) block' (f block')
          end
        in
      let statement_mut_cases :=
        fix f (cases: list StatementSwitchCase) : P3 cases :=
          match cases with
          | nil => H16
          | cons case_first cases' =>
            let Hcase := match case_first with
            | StatSwCaseAction tags label code =>
              H18 tags label code (statement_mut_block code)
            | StatSwCaseFallThrough tags label => H19 tags label
            end in H17 case_first Hcase cases' (f cases')
          end
        in
      match stmt as x return P x with
      | MkStatement tag stmt_pre typ =>
        let Hblock := match stmt_pre as x return P0 x with
        | StatMethodCall func type_args args => H1 func type_args args
        | StatAssignment lhs rhs => H2 lhs rhs
        | StatDirectApplication typ args => H3 typ args
        | StatConditional cond tru None => H4 cond tru (statement_mut tru)
        | StatConditional cond tru (Some fls) =>
          H5 cond tru fls (statement_mut tru) (statement_mut fls)
        | StatBlock block => H6 block (statement_mut_block block)
        | StatExit => H7
        | StatEmpty => H8
        | StatReturn expr => H9 expr
        | StatSwitch expr cases => H10 expr cases (statement_mut_cases cases)
        | StatConstant typ name value => H11 typ name value
        | StatVariable typ name init => H12 typ name init
        | StatInstantiation typ args name init => H13 typ args name init
        end in H0 tag stmt_pre Hblock typ
      end
    .

  End statement_mut_ind.

  Inductive ParserCase :=
  | MkParserCase (tags: tags_t) (matches: list Match) (next: P4String).

  Inductive ParserTransition :=
  | ParserDirect (tags: tags_t) (next: P4String)
  | ParserSelect (tags: tags_t) (exprs: list Expression) (cases: list ParserCase).

  Inductive ParserState :=
  | MkParserState (tags: tags_t)  (name: P4String)
                  (statements: list Statement) (transition: ParserTransition).

  Inductive DeclarationField :=
  | MkDeclarationField (tags: tags_t)  (typ: P4Type)
                       (name: P4String).

  Inductive Declaration :=
  | DeclConstant (tags: tags_t)  (typ: P4Type)
                 (name: P4String) (value: ValueBase)
  | DeclInstantiation (tags: tags_t)  (typ: P4Type)
                      (args: list Expression) (name: P4String)
                      (init: option (list Statement))
  | DeclParser (tags: tags_t)  (name: P4String)
               (type_params: list P4String) (params: list P4Parameter)
               (constructor_params: list P4Parameter)
               (locals: list Declaration) (states: list ParserState)

  | DeclControl (tags: tags_t)  (name: P4String)
                (type_params: list P4String) (params: list P4Parameter)
                (constructor_params: list P4Parameter) (locals: list Declaration)
                (apply: list Statement)
  | DeclFunction (tags: tags_t) (ret: P4Type) (name: P4String)
                 (type_params: list P4String) (params: list P4Parameter)
                 (body: list Statement)
  | DeclExternFunction (tags: tags_t)  (ret: P4Type)
                       (name: P4String) (type_params: list P4String)
                       (params: list P4Parameter)
  | DeclVariable (tags: tags_t)  (typ: P4Type)
                 (name: P4String) (init: option Expression)
  | DeclValueSet (tags: tags_t)  (typ: P4Type)
                 (size: Expression) (name: P4String)
  | DeclAction (tags: tags_t)  (name: P4String)
               (data_params: list P4Parameter) (ctrl_params: list P4Parameter)
               (body: list Statement)
  | DeclTable (tags: tags_t)  (name: P4String)
              (key: list TableKey) (actions: list TableActionRef)
              (entries: option (list TableEntry))
              (default_action: option TableActionRef) (size: option P4Int)
              (custom_properties: list TableProperty)
  | DeclHeader (tags: tags_t)  (name: P4String)
               (fields: list DeclarationField)
  | DeclHeaderUnion (tags: tags_t)  (name: P4String)
                    (fields: list DeclarationField)
  | DeclStruct (tags: tags_t)  (name: P4String)
               (fields: list DeclarationField)
  | DeclError (tags: tags_t) (members: list P4String)
  | DeclMatchKind (tags: tags_t) (members: list P4String)
  | DeclEnum (tags: tags_t)  (name: P4String)
             (members: list P4String)
  | DeclSerializableEnum (tags: tags_t)  (typ: P4Type)
                         (name: P4String) (members: list (P4String * Expression))
  | DeclExternObject (tags: tags_t)  (name: P4String)
                     (type_params: list P4String) (methods: list MethodPrototype)
  | DeclTypeDef (tags: tags_t)  (name: P4String)
                (typ_or_decl: (P4Type + Declaration))
  | DeclNewType (tags: tags_t)  (name: P4String)
                (typ_or_decl: (P4Type + Declaration))
  | DeclControlType (tags: tags_t)  (name: P4String)
                    (type_params: list P4String) (params: list P4Parameter)
  | DeclParserType (tags: tags_t)  (name: P4String)
                   (type_params: list P4String) (params: list P4Parameter)
  | DeclPackageType (tags: tags_t)  (name: P4String)
                    (type_params: list P4String) (params: list P4Parameter).

  Definition ValueLoc := String.t.

  Inductive ValueTable :=
  | MkValTable (name: String.t) (keys: list TableKey)
               (actions: list TableActionRef) (default_action: TableActionRef)
               (const_entries: list TableEntry).

  Definition Env_env binding := list (list (String.t * binding)).

  Inductive Env_EvalEnv :=
  | MkEnv_EvalEnv (vs: Env_env ValueLoc) (typ: Env_env P4Type) (namespace: String.t).

  Inductive ValuePreLvalue :=
  | ValLeftName (name: Typed.name)
  | ValLeftMember (expr: ValueLvalue) (name: String.t)
  | ValLeftBitAccess (expr: ValueLvalue) (msb: nat) (lsb: nat)
  | ValLeftArrayAccess (expr: ValueLvalue) (idx: nat)
  with ValueLvalue :=
  | MkValueLvalue (lvalue: ValuePreLvalue) (typ: P4Type).

  Inductive ValueFunctionImplementation :=
  | ValFuncImplUser (scope: Env_EvalEnv) (body: list Statement)
  | ValFuncImplExtern (name: String.t) (caller: option (ValueLoc * String.t))
  | ValFuncImplBuiltin (name: String.t) (caller: ValueLvalue).

  Inductive ValueObject :=
  | ValObjParser (scope: Env_EvalEnv)
                 (params: list P4Parameter) (locals: list Declaration)
                 (states: list ParserState)
  | ValObjTable (_: ValueTable)
  | ValObjControl (scope: Env_EvalEnv)
                  (params: list P4Parameter) (locals: list Declaration)
                  (apply: list Statement)
  | ValObjPackage (args: list (String.t * ValueLoc))
  | ValObjRuntime (loc: ValueLoc) (obj_name: String.t)
  | ValObjFun (params: list P4Parameter) (impl: ValueFunctionImplementation)
  | ValObjAction (scope: Env_EvalEnv) (params: list P4Parameter)
                 (body: list Statement)
  | ValObjPacket (bits: list bool).

  Inductive ValueConstructor :=
  | ValConsParser (scope: Env_EvalEnv) (constructor_params: list P4Parameter)
                  (params: list P4Parameter) (locals: list Declaration)
                  (states: list ParserState)
  | ValConsTable (_: ValueTable)
  | ValConsControl (scope: Env_EvalEnv) (constructor_params: list P4Parameter)
                   (params: list P4Parameter) (locals: list Declaration)
                   (apply: list Statement)
  | ValConsPackage (params: list P4Parameter) (args: list (String.t * ValueLoc))
  | ValConsExternObj (_: list (String.t * list P4Parameter)).

  Inductive Value :=
  | ValBase (_: ValueBase)
  | ValObj (_: ValueObject)
  | ValCons (_: ValueConstructor)
  | ValLvalue (_: ValueLvalue).

  (* Value_entries, Value_vset, Value_ctrl, Value_signal omitted*)

  Inductive program := Program (_: list Declaration).

End Syntax.
