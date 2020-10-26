module I = Info
open Target
open Prog
open Env
open Value
open Core_kernel
open Typed
module Info = I
let (=) = Stdlib.(=)
let (<>) = Stdlib.(<>)

module PreUp4Filter : Target = struct

  (* TODO: Define uP4 obj *)
  type obj = 
    | Packet of {pck: int list; size: int} (* represented as a byte array *)
    (*
    | IM_T of {}  (* intrinsic metadata and constraints *)
    | emitter (* assemble packets *)
    | extractor (* header extraction *)
    | in_buf (* input buffer *)
    | out_buf (* output buffer *)
    *)

  let dummy = Packet {pck = []; size = 0}

  type state = obj State.t

  type extern = state pre_extern

  (* TODO: Implement uP4 externs *)

  (* Create instances of pkt extern *)
  let eval_copy_from : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_get_length : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_set_out_port : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_get_in_port : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_get_out_port : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_get_value : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_drop : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_emit : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_extract : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_lookahead : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_dequeue : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_enqueue : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_to_in_buf : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  let eval_merge : extern = fun env st ts args -> 
    env, st, SContinue, VNull

  (* stp: never actually used; see note in v1model.ml *)
  let externs = [
    ("copy_from", eval_copy_from); (* Overloaded. input type is pkt or im_t *)
    ("get_length", eval_get_length);
    ("set_out_port", eval_set_out_port);
    ("get_in_port", eval_get_in_port); 
    ("get_out_port", eval_get_out_port);
    ("get_value", eval_get_value);
    ("drop", eval_drop);
    ("emit", eval_emit);
    ("extract", eval_extract);
    ("lookahead", eval_lookahead);
    ("dequeue", eval_dequeue);
    ("enqueue", eval_enqueue); 
    ("to_in_buf", eval_to_in_buf);
    ("merge", eval_merge);
  ]

  let read_header_field : obj reader = fun is_valid fields fname ->
    List.Assoc.find_exn fields fname ~equal:String.equal

  let write_header_field : obj writer = fun is_valid fields fname fvalue ->
    let fs = List.map fields
      ~f:(fun (n,v) -> if String.equal n fname then n, fvalue else n,v) in
    VHeader {fields = fs; is_valid; }

  let assign_lvalue = assign_lvalue read_header_field write_header_field

  let eval_extern name =
    match name with
    | "copy_from" -> eval_copy_from (* Overloaded. input type is pkt or im_t *)
    | "get_length" -> eval_get_length
    | "set_out_port" -> eval_set_out_port
    | "get_in_port" -> eval_get_in_port 
    | "get_out_port" -> eval_get_out_port
    | "get_value" -> eval_get_value
    | "drop" -> eval_drop
    | "emit" -> eval_emit
    | "extract" -> eval_extract
    | "lookahead" -> eval_lookahead
    | "dequeue" -> eval_dequeue
    | "enqueue" -> eval_enqueue 
    | "to_in_buf" -> eval_to_in_buf
    | "merge" -> eval_merge
    | _ -> failwith "extern unknown in up4 or not yet implemented"

  let initialize_metadata meta st =
    State.insert_heap "__INGRESS_PORT__" (VInteger meta) st

  let check_pipeline env = failwith "unimplemented"

  let eval_ebpf_ctrl (ctrl : ctrl) (control : value) (args : Expression.t option list) app
  (env,st) : state * signal =
    let (st,s,_) = app ctrl env st SContinue control args in 
    (st,s)

  (* TODO: unsure of type of this method.. *)
  (* let eval_up4_ctrl = 
    failwith "unimplemented" *)

  (* Update state and environment with parser params, and 
     return processed parser params that can be used in running the apply. *)
  let helper (env: env) (st: state) (paramStrings: string list) 
             (params: Parameter.t list): 
             state * env * (Info.t * Expression.typed_t) option list = 
    let locs = List.map paramStrings ~f:(fun _ -> State.fresh_loc ()) in 
    let namesToLocs = List.mapi paramStrings ~f:(fun i pString -> 
        Types.BareName (Info.dummy, pString), List.nth_exn locs i) in 
    let locsToValues = List.mapi params ~f:(fun i param -> 
        let loc = List.nth_exn locs i in 
        if i = 0 then loc, VRuntime {loc = State.packet_location; 
                                     obj_name = "packet_in"; } 
        else loc, init_val_of_typ env param.typ) in
    let updatedState = List.fold_left locsToValues ~init:st 
        ~f:(fun st' (loc, value) -> State.insert_heap loc value st') in 
    let updatedEnv = List.fold_left namesToLocs ~init:env 
        ~f:(fun env' (name, loc) -> EvalEnv.insert_val name loc env') in
    let open Expression in
    let exprs = List.mapi namesToLocs ~f:(fun i (name, _) -> 
        Some (Info.dummy, {expr = Name name; 
                           dir = (List.nth_exn params i).direction; 
                           typ = (List.nth_exn params i).typ})) in
      updatedState, updatedEnv, exprs

  (* hj283: push [pkt] through pipeline of this architecture, 
     updating the environment and state and return the 
     new state, environment and the packet if it was accepted! *)
  let eval_pipeline (ctrl : ctrl) (env : env) (st : state) (pkt : pkt)
      (app : state apply) : state * env * pkt option =
    (* Get main   *)
    let main = State.find_heap (EvalEnv.find_val (BareName (Info.dummy, "main")) env) st in
    (* Get arguments passed into main *)
    let vs = assert_package main |> snd in
    (* Get Package parameters *)
    let parser = List.Assoc.find_exn vs "p" ~equal:String.equal |> fun x -> State.find_heap x st in
    (* let control = List.Assoc.find_exn vs "c" ~equal:String.equal |> fun x -> State.find_heap x st in *)
    let deparser = List.Assoc.find_exn vs "d" ~equal:String.equal |> fun x -> State.find_heap x st in
    (* *)
    let params =
      match parser with
      | VParser {pparams=ps;_} -> ps
      | _ -> failwith "parser is not a parser object" in
    let deparse_params = 
      match deparser with 
      | VControl {cparams=ps;_} -> ps
      | _ -> failwith "deparser is not a control object" in 
    ignore deparse_params;
    let vpkt = VRuntime {loc = State.packet_location; obj_name = "packet_in"; } in
    let pkt_name = Types.BareName (Info.dummy, "packet") in
    let im = init_val_of_typ env (List.nth_exn params 1).typ in 
    let im_name = Types.BareName (Info.dummy, "im") in 
    let hdrs = init_val_of_typ env (List.nth_exn params 2).typ in
    let hdrs_name = Types.BareName (Info.dummy, "hdrs") in
    let meta = init_val_of_typ env (List.nth_exn params 3).typ in
    let meta_name = Types.BareName (Info.dummy, "meta") in
    let in_p = init_val_of_typ env (List.nth_exn params 4).typ in
    let in_p_name = Types.BareName (Info.dummy, "in_param") in
    let inout_p = init_val_of_typ env (List.nth_exn params 5).typ in
    let inout_p_name = Types.BareName (Info.dummy, "inout_param") in
    let vpkt_loc, im_loc, hdrs_loc, meta_loc, in_p_loc, inout_p_loc = 
      State.fresh_loc (),  State.fresh_loc (), State.fresh_loc (), State.fresh_loc (), State.fresh_loc (), State.fresh_loc () in
    (* Types.BareName is repetitive, maybe put im, hdrs,meta... through a function to create
    the types.BareNames. Possibly save params into a list and run List.map to generate var names.
    p is for param  *)
    (* Update state *)
    let st = st
      |> State.insert_heap vpkt_loc vpkt
      |> State.insert_heap im_loc im
      |> State.insert_heap hdrs_loc hdrs
      |> State.insert_heap meta_loc meta
      |> State.insert_heap in_p_loc in_p
      |> State.insert_heap inout_p_loc inout_p in
    (* Update environment *)
    let env =
      EvalEnv.(env
              |> insert_val pkt_name     vpkt_loc
              |> insert_val im_name      im_loc
              |> insert_val hdrs_name    hdrs_loc
              |> insert_val meta_name    meta_loc
              |> insert_val in_p_name    in_p_loc
              |> insert_val inout_p_name inout_p_loc
              |> insert_typ pkt_name     (List.nth_exn params 0).typ
              |> insert_typ im_name      (List.nth_exn params 1).typ 
              |> insert_typ hdrs_name    (List.nth_exn params 2).typ
              |> insert_typ meta_name    (List.nth_exn params 3).typ
              |> insert_typ in_p_name    (List.nth_exn params 4).typ
              |> insert_typ inout_p_name (List.nth_exn params 5).typ) in
              let open Expression in
    let pkt_expr =
      Some (Info.dummy, {expr = Name pkt_name; dir = InOut; typ = (List.nth_exn params 0).typ}) in
    let im_expr = (* Are we doing this right? *)
      Some (Info.dummy, {expr = Name im_name; dir = Directionless; typ = (List.nth_exn params 1).typ}) in
    let hdrs_expr =
      Some (Info.dummy, {expr = Name hdrs_name; dir = Out; typ = (List.nth_exn params 2).typ}) in
    let meta_expr =
      Some (Info.dummy, {expr = Name meta_name; dir = InOut; typ = (List.nth_exn params 3).typ}) in
    let in_expr =
      Some (Info.dummy, {expr = Name in_p_name; dir = In; typ = (List.nth_exn params 4).typ}) in
    let inout_expr =
      Some (Info.dummy, {expr = Name inout_p_name; dir = InOut; typ = (List.nth_exn params 5).typ}) in
    let (st,state, _) =
      app ctrl env st SContinue parser [pkt_expr; im_expr; hdrs_expr; meta_expr; in_expr; inout_expr] in
    (** Do we need to do set namespace?
    let env = EvalEnv.set_namespace "" env *)
    match state with 
    (** TODO: implement up4 actions based off of state result.
        TODO: write eval_up4_ctrl *)
    | SReject _ -> st, env, None
    | SContinue | SExit | SReturn _ -> st, env, None

  (* TODO: implement *)
  let get_outport (st : state) (env : env) : Bigint.t =
    State.find_heap "__INGRESS_PORT__" st |> bigint_of_val
    (* failwith "unimplemented" *)

  end 

module Up4Filter : Target = P4core.Corize(PreUp4Filter)
