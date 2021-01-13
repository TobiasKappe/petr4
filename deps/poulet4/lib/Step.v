Require Import Coq.Lists.List.
Require Import Syntax.
Require Import Eval.
Require Import Environment.
Require Import Monads.Monad.
Require Import Monads.State.
Require String.

Open Scope monad.

Section Step.
  Context (tags_t: Type).
  Context (tags_dummy: tags_t).

  Fixpoint lookup_state (states: list (ParserState tags_t)) (name: String.t) : option (ParserState tags_t) :=
    match states with
    | List.nil => None
    | s :: states' =>
      let 'MkParserState _ _ (MkP4String _ _ s_name) _ _ := s in
      if String.eqb name s_name
      then Some s
      else lookup_state states' name
    end.

  Definition step (p: (ValueObject tags_t)) (start: String.t) : env_monad tags_t String.t :=
    match p with
    | ValObjParser _ env params locals states =>
      match lookup_state states start with
      | Some nxt =>
        let 'MkParserState _ _ _ statements transition := nxt in
        let blk := StatBlock _ statements in
        let* _ := eval_statement _ tags_dummy (MkStatement _ tags_dummy blk Typed.StmUnit) in
        eval_transition tags_t tags_dummy transition
      | None =>
        state_fail Internal
      end
    | _ => state_fail Internal
    end.

  (* TODO: formalize progress with respect to a header, such that if the parser
  always makes forward progress then there exists a fuel value for which
  the parser either rejects or accepts (or errors, but not due to lack of fuel)
   *)
  Fixpoint step_trans (p: ValueObject tags_t) (fuel: nat) (start: String.t) : env_monad tags_t unit :=
    match fuel with
    | 0   => state_fail Internal (* TODO: add a separate exception for out of fuel? *)
    | S x => let* state' := step p start in
            if String.eqb state' String.accept
            then mret tt
            else if String.eqb state' String.reject
            then state_fail Reject
            else step_trans p x state'
    end.

End Step.
