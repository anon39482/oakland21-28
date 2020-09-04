open Utils
open Prog
open Apron
open ToEC
open Wsize

exception Aint_error of string

(*------------------------------------------------------------*)
let last_time = ref 0.;;

let print_time a =
  let t = Sys.time () in
  let diff = t -. !last_time in
  last_time := t;
  Format.eprintf "Time: %1.3f s. (+ %1.3f s.)@." t diff;
  a ()

let debug_print_time = true

let debug a = 
  if !Glob_options.debug then
    if debug_print_time then print_time a else a ()
  else ()

let () = debug (fun () ->
    Format.eprintf "Debug: record backtrace@.";
    Printexc.record_backtrace true);;


(*------------------------------------------------------------*)
(* REM *)
(* Printexc.record_backtrace true *)

let hndl_apr_exc e = match e with
  | Manager.Error exclog as e ->
    Printexc.print_backtrace stderr;
    Format.eprintf "@[<v>Apron error message:@;@[%a@]@;@]@."
      Manager.print_exclog exclog;
    raise e
  | _ as e -> raise e


(***********************)
(* Analysis Parameters *)
(***********************)


(* Analysis strategy for abstract calls:
   - Call_Direct: normal abstract function call.
   - Call_TopByCallSite : function evaluated only once per call-site, with
     an initial state over-approximated by top.
     (FIXME: performance: evaluates only once on top). *)
type abs_call_strategy =
  | Call_Direct 
  | Call_TopByCallSite 
   (* - Call_WideningByCallSite: normal abstact function call, but with
    *   successive widenings of the initial states at each call to the same
    *   function, from the same call-site.
    *   | Call_WideningByCallSite *)

(* Analysis policy for abstract calls. *)
type abs_call_policy =
  | CallDirectAll
  | CallTopHeuristic
  (* | CallWideningAll *)

module Aparam = struct
  (* Number of unrolling of a loop body before applying the widening. Higher
     values yield a more precise (and more costly) analysis. *)
  let k_unroll = 1;;

  assert (k_unroll >= 0)

  (* Rounding used. *)
  let round_typ = Texpr1.Zero

  let abs_call_strategy = CallDirectAll (* CallTopHeuristic *) 

  (* Widening outside or inside loops.
     Remark: if the widening is done inside loops, then termination is not
     guaranteed in general. Nonetheless, if the meet operator is monotonous
     then this should always terminates. *)
  let widening_out = false

  (* Zero thresholds for the widening. *)
  let zero_threshold = true

  (* Thresholds from the analysis parameters for the widening. *)
  let param_threshold = true

    (* More thresholds for the widening. *)
  let more_threshold = false

  (* Dependency graph includes flow dependencies *)
  let flow_dep = false

  (* Add disjunction with if statement when possible *)
  let if_disj = true

  (* Try to enrich the widening of A and B with the constraints of A 
     that are satisfied by B. *)
  (* let enrich_widening = true *)

  (* Handle top-level conditional move and if expressions as if statements.
     Combinatorial explosion if there are many movecc and if expressions in the
     same block. *)
  let pif_movecc_as_if = true

  (* Pre-analysis looks for the variable corresponding to return boolean 
     flags appearing in while loop condition (adding them to the set of 
     variables in the relational domain). *)
  let while_flags_setfrom_dep = true

  (***********************)
  (* Printing parameters *)
  (***********************)

  (* Turn on printing of array variables *)
  let arr_no_print = true       (* default: true*)

  (* Turn on printing of global variables *)
  let glob_no_print = true      (* default: true *)

  (* Turn on printing of non-relational variables *)
  let nrel_no_print = ref false (* default: false *)

  (* Turn on printing of unconstrained variables *)
  let ignore_unconstrained = true (* default: true *)

  type init_print = IP_None | IP_NoArray | IP_All
  (* Turn on printing of not initialized variables 
     (i.e. it is not certain that the variable is initialized). *)
  let is_init_no_print = IP_None   (* defaul: IP_None *)

  (* Turn on printing of boolean variables *)
  let bool_no_print = true   (* defaul: true *)


  (****************)
  (* Miscelaneous *)
  (****************)
  (* Should the function name be appended to the variable name. *)
  let var_append_fun_name = false
end

(* Turn on printing of only the relational part *)
let only_rel_print = ref false

(*************************)
(* Unique Variable Names *)
(*************************)

module MkUniq : sig

  val mk_uniq : unit func -> unit prog -> (unit func * unit prog)

end = struct
  let ht_uniq = Hashtbl.create ~random:false 16

  let htv = Hashtbl.create ~random:false 16

  let rec mk_gv v = v ^ "##g"

  and mk_glob (ws, t, i) = (ws, mk_gv t, i)

  and mk_globs globs = List.map mk_glob globs

  and mk_f f_decl =
    { f_decl with
      f_args = List.map (mk_v f_decl.f_name.fn_name) f_decl.f_args;
      f_body = mk_stmt f_decl.f_name.fn_name f_decl.f_body;
      f_ret = List.map (mk_v_loc f_decl.f_name.fn_name) f_decl.f_ret }

  and mk_v fn v =
    let short_name v = v.v_name ^ "." ^ (string_of_int (int_of_uid v.v_id)) in
    let long_name v =
      if Aparam.var_append_fun_name 
      then (short_name v) ^ "#" ^ fn
      else short_name v
    in

      if Hashtbl.mem htv (short_name v, fn) then
        Hashtbl.find htv (short_name v, fn)
      else if Hashtbl.mem ht_uniq v.v_name then
        let nv = V.mk (long_name v) v.v_kind v.v_ty v.v_dloc in
        let () = Hashtbl.add htv (short_name v, fn) nv in
        nv
      else
        let () = Hashtbl.add ht_uniq v.v_name () in
        let () = Hashtbl.add htv (short_name v, fn) v in
        v

  and mk_v_loc fn v = L.mk_loc (L.loc v) (mk_v fn (L.unloc v))

  and mk_lval fn lv = match lv with
    | Lnone _ -> lv
    | Lvar v -> Lvar (mk_v_loc fn v)
    | Lmem (ws,ty,e) -> Lmem (ws, mk_v_loc fn ty, mk_expr fn e)
    | Laset (ws,v,e) -> Laset (ws, mk_v_loc fn v, mk_expr fn e)

  and mk_range fn (dir, e1, e2) = (dir, mk_expr fn e1, mk_expr fn e2)

  and mk_lvals fn lvs = List.map (mk_lval fn) lvs

  and mk_instr fn st = { st with i_desc = mk_instr_r fn st.i_desc }

  and mk_instr_r fn st = match st with
    | Cassgn (lv, tag, ty, e) ->
      Cassgn (mk_lval fn lv, tag, ty, mk_expr fn e)
    | Copn (lvls, tag, opn, exprs) ->
      Copn (mk_lvals fn lvls, tag, opn, mk_exprs fn exprs)
    | Cif (e, st, st') ->
      Cif (mk_expr fn e, mk_stmt fn st, mk_stmt fn st')
    | Cfor (v, r, st) ->
      Cfor (mk_v_loc fn v, mk_range fn r, mk_stmt fn st)
    | Ccall (inlinf, lvs, c_fn, es) ->
      Ccall (inlinf, mk_lvals fn lvs, c_fn, mk_exprs fn es)
    | Cwhile (a, st1, e, st2) ->
      Cwhile (a, mk_stmt fn st1, mk_expr fn e, mk_stmt fn st2)

  and mk_stmt fn instrs = List.map (mk_instr fn) instrs

  and mk_expr fn expr = match expr with
    | Pconst _ | Pbool _ | Parr_init _ -> expr
    | Pglobal (ws,t) -> Pglobal (ws, mk_gv t)
    | Pvar v -> Pvar (mk_v_loc fn v)
    | Pget (ws, v, e) -> Pget (ws, mk_v_loc fn v, mk_expr fn e)
    | Pload (ws, v, e) -> Pload (ws, mk_v_loc fn v, mk_expr fn e)
    | Papp1 (op, e) -> Papp1 (op, mk_expr fn e)
    | Papp2 (op, e1, e2) -> Papp2 (op, mk_expr fn e1, mk_expr fn e2)
    | PappN (op,es) -> PappN (op, List.map (mk_expr fn) es)
    | Pif (ty, e, el, er)  ->
      Pif (ty, mk_expr fn e, mk_expr fn el, mk_expr fn er)

  and mk_exprs fn exprs = List.map (mk_expr fn) exprs

  let mk_uniq main_decl (glob_decls, fun_decls) =
    Hashtbl.clear ht_uniq;
    Hashtbl.clear htv;

    let m_decl = mk_f main_decl in
    (m_decl, (mk_globs glob_decls, List.map mk_f fun_decls))

end


(*******************)
(* Pretty Printers *)
(*******************)

let pp_apr_env ppf e = Environment.print ppf e;;

let rec pp_list ?sep:(msep = Format.pp_print_space) pp_el fmt l = match l with
  | [] -> Format.fprintf fmt ""
  | h :: t -> Format.fprintf fmt "%a%a%a" pp_el h msep ()
                (pp_list ~sep:msep pp_el) t;;

let pp_opt pp_el fmt = function
  | None -> Format.fprintf fmt "None"
  | Some el -> Format.fprintf fmt "Some @[%a@]" pp_el el

let pp_call_strategy fmt = function
  | Call_Direct             -> Format.fprintf fmt "direct"
  | Call_TopByCallSite      -> Format.fprintf fmt "top"
  (* | Call_WideningByCallSite -> Format.fprintf fmt "widening" *)


(*************)
(* Profiling *)
(*************)

let rec assoc_up s f = function
  | [] -> raise Not_found
  | (a,b) :: t ->
    if a = s then (a, f b) :: t
    else (a,b) :: assoc_up s f t

module Prof : sig
  val record : string -> unit
  val is_recorded : string -> bool
  val call : string -> float -> unit
  val reset_all : unit -> unit

  val print : Format.formatter -> unit -> unit
end = struct
  let lrec = ref []

  let record s =
    let () = assert (not (List.mem_assoc s !lrec)) in
    lrec := (s,(0,0.)) :: !lrec;;

  let is_recorded s = List.mem_assoc s !lrec

  let call s t =
    lrec := assoc_up s (fun (x,t') -> (x + 1,t +. t')) !lrec;;
  
  let reset_all () = lrec := []

  let print fmt () =
    let pp_el fmt (a, (b,f)) =
      Format.fprintf fmt "%10d %s : %1f seconds" b a f in

    Format.fprintf fmt "@[<v>Statistiques:@;@[<v>%a@]@]@."
      (pp_list pp_el) (List.sort (fun (a,(_,f)) (a',(_,f')) ->
          if a = a' then 0
          else if f > f' then -1 else 1) !lrec)
end


(************************)
(* Abstract Environment *)
(************************)

(* Memory locations *)
type mem_loc = MemLoc of ty gvar

type atype =
  | Avar of ty gvar                     (* Variable *)
  | Aarray of ty gvar                   (* Array *)
  | AarrayEl of ty gvar * wsize * int   (* Array element *)

type mvar =
  | Temp of string * int * ty   (* Temporary variable *)
  | WTemp of string * int * ty  (* Temporary variable (weak updates) *)
  | Mglobal of Name.t * ty      (* Global variable *)
  | Mvalue of atype             (* Variable value *)
  | MinValue of ty gvar         (* Variable initial value *)
  | MvarOffset of ty gvar       (* Variable offset *)
  | MNumInv of L.t              (* Numerical Invariants *)
  | MmemRange of mem_loc        (* Memory location range *)

(* Must the variable [v] be handled as a weak variable, under
   standard semantics (not is_spec) or speculative semantics (is_spec).
   Under speculative semantics, all stores to non-register variables can be
   re-ordered. Consequently, such variables must be weak variables. *)
let weak_update is_spec v = 
  let weak_update_kind = function
    | Const -> assert false     (* should not happen *)
    | Stack  -> is_spec
    | Reg  
    | Inline
    | Global -> false in

  match v with
  | Mglobal _ -> false (* global variable are read-only. *)
  | Temp _
  | MNumInv _ -> 
    (* we do not check termination under the speculative semantics *)
    assert (not is_spec); 
    false

  | Mvalue at -> begin match at with
      | Avar gv | Aarray gv | AarrayEl (gv,_,_) -> weak_update_kind gv.v_kind
    end

  | MinValue gv
  | MvarOffset gv ->  weak_update_kind gv.v_kind 

  | MmemRange _ -> true
  | WTemp _ -> true

let string_of_mloc = function
  | MemLoc s -> s.v_name

let string_of_atype = function
  | Avar s -> "v_" ^ s.v_name
  | Aarray t -> "a_" ^ t.v_name
  | AarrayEl (t,ws,int) ->
    Format.asprintf "ael_%s_%d_%d" t.v_name (int_of_ws ws) int

let string_of_mvar = function
  | Temp (s, i, _) -> "tmp_" ^ s ^ "_" ^ string_of_int i
  | WTemp (s, i, _) -> "wtmp_" ^ s ^ "_" ^ string_of_int i
  | Mglobal (n,_) -> "g_" ^ n
  | MinValue s -> "inv_" ^ s.v_name
  | Mvalue at -> string_of_atype at
  | MvarOffset s -> "o_" ^ s.v_name
  | MNumInv lt -> "ni_" ^ string_of_int (fst lt.loc_start)
  | MmemRange loc -> "mem_" ^ string_of_mloc loc

let pp_mvar fmt v = Format.fprintf fmt "%s" (string_of_mvar v)

let dummy_mvar = Mvalue (Avar (V.mk "__absint_empty_env"
                                 Reg (Bty (U U8)) (L._dummy)))


let svariables_ignore vs =
  match String.split_on_char '_' vs with
  | [] -> assert false
  | vs' :: _ -> match String.split_on_char '@' vs' with
    | "inv" :: _ -> true
    | "ael" :: _  -> Aparam.arr_no_print
    | "g" :: _  -> Aparam.glob_no_print
    | _ -> false

let variables_ignore v =
  let vs = Var.to_string v in
  svariables_ignore vs

let arr_range v = match v.v_ty with
  | Arr (_,i) -> i
  | _ -> assert false

let arr_size v = match v.v_ty with
  | Arr (ws,_) -> ws
  | _ -> assert false

let ty_atype = function
  | Avar s -> s.v_ty
  | Aarray t -> t.v_ty
  | AarrayEl (_,ws,_) -> Bty (U ws)

let ty_mvar = function
  | Temp (_,_,ty) -> ty
  | WTemp (_,_,ty) -> ty
  | Mglobal (_,ty) -> ty
  | MinValue s -> s.v_ty
  | Mvalue at -> ty_atype at
  | MvarOffset _ -> Bty Int
  | MNumInv _ -> Bty Int
  | MmemRange _ -> Bty Int

(* We log the result to be able to inverse it. *)
let log_var = Hashtbl.create 16
    
let avar_of_mvar a =
  let s = string_of_mvar a in
  if not(Hashtbl.mem log_var s) then
    Hashtbl.add log_var s a;
  Var.of_string s

let mvar_of_svar s =
  try Hashtbl.find log_var s with
  | Not_found ->
    Format.eprintf "mvar_of_svar: unknown variable %s@." s;
    assert false

let mvar_of_avar v =
  let s = Var.to_string v in
  mvar_of_svar s

(* Blasts array elements and arrays. *)
let u8_blast_at ~blast_arrays at = match at with
  | Aarray v ->
    if blast_arrays then
      let iws = (int_of_ws (arr_size v)) / 8 in
      let r = arr_range v in
      let vi i = Mvalue (AarrayEl (v,U8,i)) in
      List.init (r * iws) vi
    else [Mvalue at]
        
  | AarrayEl (v,ws,j) ->
    let iws = (int_of_ws ws) / 8 in
    let vi i = Mvalue (AarrayEl (v,U8,i + iws * j )) in
    List.init iws vi
  | _ -> [Mvalue at]

let u8_blast_var ~blast_arrays v = match v with
  | Mvalue at -> u8_blast_at ~blast_arrays at
  | _ -> [v]

let u8_blast_ats ~blast_arrays ats =
  List.flatten (List.map (u8_blast_at ~blast_arrays) ats)

let u8_blast_vars ~blast_arrays vs =
  List.flatten (List.map (u8_blast_var ~blast_arrays) vs)

let rec expand_arr_vars = function
  | [] -> []
  | Mvalue (Aarray v) :: t -> begin match v.v_ty with
      | Bty _ -> assert false
      | Arr (ws, n) -> List.init n (fun i -> Mvalue (AarrayEl (v,ws,i)))
                       @ expand_arr_vars t end
  | v :: t -> v :: expand_arr_vars t

let rec expand_arr_tys = function
  | [] -> []
  | Arr (ws, n) :: t ->
    List.init n (fun _ -> Bty (U ws)) @ expand_arr_tys t
  | v :: t -> v :: expand_arr_tys t

let rec expand_arr_exprs = function
  | [] -> []
  | Pvar v :: t -> begin match (L.unloc v).v_ty with
      | Arr (ws, n) ->
        List.init n (fun i -> Pget (ws, v, Pconst (B.of_int i)))
        @ expand_arr_exprs t
      | _ -> Pvar v :: expand_arr_exprs t end
  | h :: t -> h :: expand_arr_exprs t

let get_fun_def prog f = List.find_opt (fun x -> x.f_name = f) (snd prog)

let oget = function
  | Some x -> x
  | None -> raise (Failure "Oget")

type apr_env = Apron.Environment.t


(****************)
(* Pre Analysis *)
(****************)

module Pa : sig

  type dp = Sv.t Mv.t

  type cfg = Sf.t Mf.t

  (* - pa_dp: for each variable, contains the set of variables that can modify
              it. Some dependencies are ignored depending on some heuristic.
     - pa_eq: for each variable v, contains a set of variables that can be equal
              to v (function calls and direct assignments).
     - pa_cfg: control-flow graph, where an entry f -> [f1;...;fn] means that 
     f calls f1, ..., fn *)
  type pa_res = { pa_dp : dp;
                  pa_eq : dp;
                  pa_cfg : cfg;
                  while_vars : Sv.t;
                  if_conds : ty gexpr list }

  val dp_v : dp -> ty gvar -> Sv.t
  val pa_make : unit func -> unit prog -> pa_res

end = struct
  (* For each variable, we compute the set of variables that can modify it.
     Some dependencies are ignored depending on some heuristic we have. *)
  type dp = Sv.t Mv.t

  type cfg = Sf.t Mf.t

  type pa_res = { pa_dp : dp;
                  pa_eq : dp;
                  pa_cfg : cfg;
                  while_vars : Sv.t;
                  if_conds : ty gexpr list }

  let dp_v dp v = Mv.find_default Sv.empty v dp

  let add_dep dp v v' ct =
    Mv.add v (Sv.union (Sv.singleton v') (Sv.union ct (dp_v dp v))) dp

  let add_eq eq v v' =
    Mv.add v (Sv.union (Sv.singleton v') (dp_v eq v)) eq

  let cfg_v cfg f = Mf.find_default Sf.empty f cfg

  let add_call cfg f f' =
    Mf.add f (Sf.union (Sf.singleton f') (cfg_v cfg f)) cfg

  (* Dependency heuristic for variable assignment *)
  let rec app_expr dp v e ct = match e with
    | Pconst _ -> dp
    | Pbool _ -> dp
    | Parr_init _ -> dp
    | Pvar v' -> begin match (L.unloc v').v_ty with
        | Bty _ -> add_dep dp v (L.unloc v') ct
        | Arr _ -> dp end
    | Pglobal _ -> dp (* We ignore global variables  *)

    | Pget _ -> dp  (* We ignore array loads  *)

    (* We ignore loads for v, but we compute dependencies of v' in ei *)
    | Pload (_,v',ei) -> app_expr dp (L.unloc v') ei ct

    | Papp1 (_,e1) -> app_expr dp v e1 ct
    | Papp2  (_,e1,e2) -> app_expr (app_expr dp v e1 ct) v e2 ct
    | PappN (_,es) -> List.fold_left (fun dp e -> app_expr dp v e ct) dp es
    | Pif (_,b,e1,e2) ->
      app_expr (app_expr (app_expr dp v b ct) v e1 ct) v e2 ct

  (* State while building the dependency graph:
     - dp : dependency graph
     - dp : potential equalities graph
     - cfg : control-flow graph: 
             f -> [f1;...;fn] means that f calls f1, ..., fn
     - f_done : already analized functions
     - ct : variables in the context (for an example, look at the Cif case) *)
  type pa_st = { dp : dp;
                 eq : dp;
                 cfg : cfg;
                 while_vars : Sv.t;
                 if_conds : ty gexpr list;
                 f_done : Ss.t;
                 ct : Sv.t }

  (* Compute the list of variables occuring in an expression, while updating
     the state during memory loads. *)
  let expr_vars st e =
    let rec aux (acc,st) = function
      | Pconst _ | Pbool _ | Parr_init _ | Pglobal _ | Pget _ -> acc, st

      | Pvar v' -> begin match (L.unloc v').v_ty with
          | Bty _ -> (L.unloc v') :: acc, st
          | Arr _ -> acc, st end

      (* We ignore loads for v, but we compute dependencies of v' in ei *)
      | Pload (_,v',ei) ->
        let dp = app_expr st.dp (L.unloc v') ei st.ct in
        acc, { st with dp = dp }

      | Papp1 (_,e1) -> aux (acc,st) e1
      | Papp2  (_,e1,e2) -> aux (aux (acc,st) e1) e2
      | PappN (_,es) -> List.fold_left aux (acc,st) es
      | Pif (_,b,e1,e2) -> aux (aux (aux (acc,st) e1) e2) b in

    aux ([],st) e

  let st_merge st1 st2 ct =
    let mdp = Mv.merge (fun _ osv1 osv2 ->
        let sv1,sv2 = odfl Sv.empty osv1, odfl Sv.empty osv2 in
        Sv.union sv1 sv2 |> some) in
    let mcfg = Mf.merge (fun _ osf1 osf2 -> 
        let sf1,sf2 = odfl Sf.empty osf1, odfl Sf.empty osf2 in
        Sf.union sf1 sf2 |> some) in
    { dp = mdp st1.dp st2.dp;
      eq = mdp st1.eq st2.eq;
      cfg = mcfg st1.cfg st2.cfg;
      while_vars = Sv.union st1.while_vars st2.while_vars;
      f_done = Ss.union st1.f_done st2.f_done;
      if_conds = st1.if_conds @ st2.if_conds;
      ct = ct }

  let set_ct ct st = { st with ct = ct }

  let rec find_arg v vs es = match vs, es with
    | [],_ | _, [] -> assert false
    | v' :: vs', e' :: es' -> if v' = v then e' else find_arg v vs' es'

  let pa_expr st v e = { st with dp = app_expr st.dp v e st.ct }

  let pa_eq st v e = match e with
    | Pvar v' -> { st with eq = add_eq st.eq v (L.unloc v')}
    | _ -> st

  let pa_lv st lv e = match lv with
    | Lnone _ | Laset _ -> st   (* We ignore array stores *)
    | Lvar v -> pa_expr st (L.unloc v) e

    (* For memory stores, we are only interested in v and ei *)
    | Lmem (_, v, ei) -> pa_expr st (L.unloc v) ei


  let rec flag_mem_lvs v = function
    | [] -> false
    | Lnone _ :: t | Lmem _ :: t | Laset _ :: t -> flag_mem_lvs v t
    | Lvar v' :: t -> v = L.unloc v' || flag_mem_lvs v t
                   
  exception Flag_set_from_failure
  (* Try to find the left variable of the last assignment(s) where the flag 
     v was set. *)
  let rec pa_flag_setfrom v = function
    | [] -> None
    | i :: t -> let i_opt = pa_flag_setfrom_i v i in
      if is_none i_opt then pa_flag_setfrom v t else i_opt
  
  and pa_flag_setfrom_i v i = match i.i_desc with
    | Cassgn _ -> None
    | Copn (lvs, _, _, _) ->
      if flag_mem_lvs v lvs then
        match List.last lvs with
        | Lnone _ -> raise Flag_set_from_failure
        | Lvar r ->
          let ru = L.unloc r in
          debug(fun () -> Format.eprintf "flag %a set from %a (at %a)@."
            (Printer.pp_var ~debug:false) v
            (Printer.pp_var ~debug:false) ru
            L.pp_sloc (fst i.i_loc));
          Some ru
        | _ -> assert false
      else None

    | Cif (_, c1, c2) ->
      begin match pa_flag_setfrom v c1, pa_flag_setfrom v c2 with
        | None, None -> None
        | Some r1, Some r2 ->
          if r1 = r2 then Some r1 else raise Flag_set_from_failure
        | None, Some _ | Some _, None -> raise Flag_set_from_failure end

    | Cfor (_, _, c) ->
      pa_flag_setfrom v (List.rev c)

    | Cwhile (_, c1, _, c2) ->
      pa_flag_setfrom v ((List.rev c1) @ (List.rev c2))
        
    | Ccall (_, lvs, _, _) ->
      if flag_mem_lvs v lvs then raise Flag_set_from_failure else None        
      
  let rec pa_instr fn prog st instr = match instr.i_desc with
    | Cassgn (lv, _, _, e) -> pa_lv st lv e
    | Copn (lvs, _, _, es) -> List.fold_left (fun st lv ->
        List.fold_left (fun st e -> pa_lv st lv e) st es) st lvs

    | Cif (b, c1, c2) ->
      let vs,st = expr_vars st b in
      let st = { st with if_conds = b :: st.if_conds } in

      let st' =
        if Aparam.flow_dep then
          { st with ct = Sv.union st.ct (Sv.of_list vs) }
        else st in

      (* Note that we reset the context after the merge *)
      st_merge (pa_stmt fn prog st' c1) (pa_stmt fn prog st' c2) st.ct

    | Cfor (_, _, c) ->
      (* We ignore the loop index, since we do not use widening for loops. *)
      pa_stmt fn prog st c

    | Cwhile (_, c1, b, c2) ->
      let vs,st = expr_vars st b in

      let st' =
        if Aparam.flow_dep then
          { st with ct = Sv.union st.ct (Sv.of_list vs) }
        else st in

      let bdy_rev = (List.rev c1) @ (List.rev c2) in
      let flags_setfrom = List.fold_left (fun flags_setfrom v -> match v.v_ty with
          | Bty Bool ->
            let new_f =
              match pa_flag_setfrom v bdy_rev with
              | exception Flag_set_from_failure | None -> Sv.empty
              | Some r -> Sv.singleton r in
            Sv.union flags_setfrom new_f             
          | _ -> flags_setfrom) Sv.empty vs
      in

      let while_vars = Sv.union st'.while_vars (Sv.of_list vs) in
      let while_vars = 
        if Aparam.while_flags_setfrom_dep
        then Sv.union while_vars flags_setfrom
        else while_vars in
      
      let st' = { st' with while_vars = while_vars } in

      (* Again, we reset the context after the merge *)
      pa_stmt fn prog st' (c1 @ c2)
      |> set_ct st.ct

    | Ccall (_, lvs, fn', es) ->   
      let st = { st with cfg = add_call st.cfg fn fn' } in
      let f_decl = get_fun_def prog fn' |> oget in

      let st =
        if Ss.mem fn'.fn_name st.f_done then st
        else pa_func prog st fn' in

      let st = List.fold_left2 (fun st lv ret ->
          pa_lv st lv (Pvar ret))
          st lvs f_decl.f_ret in

      let st = List.fold_left2 pa_expr st f_decl.f_args es in

      List.fold_left2 pa_eq st f_decl.f_args es


  and pa_func prog st fn =
    let f_decl = get_fun_def prog fn |> oget in
    let st = { st with f_done = Ss.add fn.fn_name st.f_done } in
    pa_stmt fn prog st f_decl.f_body

  and pa_stmt fn prog st instrs = List.fold_left (pa_instr fn prog) st instrs

  let pa_make func prog =
    let st = { dp = Mv.empty;
               eq = Mv.empty;
               cfg = Mf.empty;
               while_vars = Sv.empty;
               f_done = Ss.empty;
               if_conds = [];
               ct = Sv.empty } in
    let st = pa_func prog st func.f_name in

    debug (fun () ->
        Format.eprintf "@[<v 2>Dependency heuristic graph:@;%a@]@."
          (pp_list (fun fmt (v, sv) -> Format.fprintf fmt "@[<hov 4>%a <-- %a@]"
                       (Printer.pp_var ~debug:true) v
                       (pp_list ( Printer.pp_var ~debug:true))
                       (List.sort (fun v v' ->
                            Stdlib.compare v.v_name v'.v_name)
                           (Sv.elements sv))))
          (List.sort (fun (v,_) (v',_) -> Stdlib.compare v.v_name v'.v_name)
             (Mv.bindings st.dp)));

    debug (fun () ->
        Format.eprintf "@[<v 2>Control-flow graph:@;%a@]@."
          (pp_list (fun fmt (f, fs) -> Format.fprintf fmt "@[<hov 4>%a --> %a@]"
                       pp_string f.fn_name
                       (pp_list (fun fmt x -> pp_string fmt x.fn_name))
                       (List.sort F.compare (Sf.elements fs))))
          (List.sort (fun (v,_) (v',_) -> F.compare v v') (Mf.bindings st.cfg)));

    { pa_dp = st.dp;
      pa_eq = st.eq;      
      pa_cfg = st.cfg;
      while_vars = st.while_vars;
      if_conds = List.sort_uniq Stdlib.compare st.if_conds }
end


(*************)
(* Mpq Utils *)
(*************)

(* Return 2^n *)
let mpq_pow n =
  let c_div = Mpq.of_int 1 in
  let mpq2 = Mpq.of_int 1 in
  Mpq.mul_2exp c_div mpq2 n;
  Mpqf.of_mpq c_div 

(* Return 2^n - y *)
let mpq_pow_minus n y =
  Mpqf.sub (mpq_pow n |> Mpqf.of_mpq) (Mpqf.of_int y)


(****************************)
(* Coeff and Interval Utils *)
(****************************)

let scalar_to_int scal =
  let tent_i = match scal with
    | Scalar.Float f -> int_of_float f
    | Scalar.Mpqf q -> Mpqf.to_float q |> int_of_float
    | Scalar.Mpfrf f -> Mpfrf.to_float f |> int_of_float in
  if Scalar.cmp_int scal tent_i = 0 then Some tent_i
  else None

let interval_to_int int =
  let open Interval in
  if Scalar.equal int.inf int.sup then scalar_to_int int.inf
  else None

let to_int c = match c with
  | Coeff.Scalar s -> Coeff.i_of_scalar s s
  | Coeff.Interval _ -> c

let s_to_mpqf = function
  | Scalar.Float f -> Mpqf.of_float f
  | Scalar.Mpqf x -> x
  | Scalar.Mpfrf f -> Mpfr.to_mpq f

let scalar_add s s' = Scalar.Mpqf (Mpqf.add (s_to_mpqf s) (s_to_mpqf s'))

let coeff_add c c' = match Coeff.reduce c, Coeff.reduce c' with
  | Coeff.Scalar s, Coeff.Scalar s' -> Coeff.Scalar (scalar_add s s')
  | _,_ ->
    match to_int c, to_int c' with
    | Coeff.Interval i, Coeff.Interval i' ->
      Coeff.Interval (Interval.of_scalar
                        (scalar_add i.inf i'.inf)
                        (scalar_add i.sup i'.sup))
    | _ -> assert false


(******************)
(* Texpr1 Wrapper *)
(******************)

module Mmv = struct
  type t = mvar

  let compare v v' = Stdlib.compare (avar_of_mvar v) (avar_of_mvar v')
  let equal v v' = avar_of_mvar v = avar_of_mvar v'
end

module Mm = Map.Make(Mmv)


module Mtexpr : sig
  type unop = Apron.Texpr0.unop
  type binop = Apron.Texpr0.binop
  type typ = Apron.Texpr0.typ
  type round = Apron.Texpr0.round

  type mexpr = private
    | Mcst of Coeff.t
    | Mvar of mvar
    | Munop of unop * mexpr * typ * round
    | Mbinop of binop * mexpr * mexpr * typ * round

  (* Careful, the environment should have already blasted array elements in
     U8 array elements. *)
  type t =  { mexpr : mexpr;
              env : apr_env }

  val to_aexpr : t -> Texpr1.t
  val to_linexpr : t -> apr_env -> Linexpr1.t option

  val cst : apr_env -> Coeff.t -> t
  val var : apr_env -> mvar -> t
  val unop : unop -> t -> t
  val binop : binop -> t -> t -> t

  val get_var_mexpr : mexpr -> mvar list
  val contains_mod : mexpr -> bool

  val extend_environment : t -> apr_env -> t

  val weak_cp : mvar -> int -> mvar
  val weak_transf : bool -> int Mm.t -> mexpr -> int Mm.t * mexpr

  (* This does not check equality of the underlying Apron environments. *)
  val equal_mexpr : t -> t -> bool

  val print : Format.formatter -> t -> unit

  val print_mexpr : Format.formatter -> mexpr -> unit
end = struct
  type unop = Texpr0.unop
  type binop = Texpr0.binop
  type typ = Apron.Texpr0.typ
  type round = Apron.Texpr0.round

  type mexpr =
    | Mcst of Coeff.t
    | Mvar of mvar
    | Munop of unop * mexpr * typ * round
    | Mbinop of binop * mexpr * mexpr * typ * round

  type t = { mexpr : mexpr;
             env : apr_env } 

  let rec e_aux = function
    | Mcst c -> Texpr1.Cst c
    | Mvar mvar -> begin match mvar with
        | Mvalue (AarrayEl (_,ws,_)) ->
          assert (ws = U8);
          Texpr1.Var (avar_of_mvar mvar)
        | _ -> Texpr1.Var (avar_of_mvar mvar) end
    | Munop (op1, a, t, r) -> Texpr1.Unop (op1, e_aux a, t, r)
    | Mbinop (op2, a, b, t, r) -> Texpr1.Binop (op2, e_aux a, e_aux b, t, r)

  let to_aexpr t = Texpr1.of_expr t.env (e_aux t.mexpr)

  let print ppf t = to_aexpr t |> Texpr1.print ppf

  let print_mexpr ppf t = e_aux t |> Texpr1.print_expr ppf

  (* Return sum_{j = 0}^{len - 1} (2^8)^(len - 1 - j) * (U8)v[offset + j] *)
  let rec build_term_array v offset len =
    let tv =
      Mvar (Mvalue (AarrayEl (v,U8,offset + len - 1))) in
    let ptwo = Mcst (Coeff.s_of_mpqf (mpq_pow (8 * (len - 1)))) in
    let t = Mbinop (Texpr1.Mul, ptwo, tv, Texpr1.Int, Aparam.round_typ) in
    if len = 1 then tv
    else Mbinop (Texpr1.Add,
                 t,
                 build_term_array v offset (len - 1),
                 Texpr1.Int, Aparam.round_typ)

  let cst env c = { mexpr = Mcst c; env = env }

  let var env v = 
    let mexpr = match v with
      | Mvalue (AarrayEl (v,ws,i)) ->
        build_term_array v (((int_of_ws ws) / 8) * i) ((int_of_ws ws) / 8)
      | _ -> Mvar v in
    { mexpr = mexpr; env = env }

  let unop op1 a = { a with
                     mexpr = Munop (op1, a.mexpr, Texpr1.Int, Aparam.round_typ) }

  let binop op2 a b =
    if not (Environment.equal a.env b.env) then
      raise (Aint_error "Environment mismatch")
    else { mexpr = Mbinop (op2, a.mexpr, b.mexpr, Texpr1.Int, Aparam.round_typ);
           env = a.env }

  let weak_cp v i = Temp ("wcp_" ^ string_of_mvar v, i, ty_mvar v)

  let to_linexpr t env =
    let exception Linexpr_failure in

    let rec linexpr t =
      match t with
      | Mvar m ->
        let l = Linexpr1.make env in
        Linexpr1.set_list l [Coeff.s_of_int 1 ,avar_of_mvar m] None;
        l

      | Mcst c ->
        let l = Linexpr1.make env in
        Linexpr1.set_cst l c;
        l

      | Munop (op, e, Texpr0.Int, _) ->
        let l = linexpr e in
        begin match op with
          | Texpr0.Neg ->
            let l' = Linexpr1.make env in
            Linexpr1.iter (fun c v -> Linexpr1.set_coeff l' v (Coeff.neg c)) l;
            Linexpr1.set_cst l' (Coeff.neg (Linexpr1.get_cst l));
            l'
          | _ -> raise Linexpr_failure end

      | Mbinop (op, e1, e2, Texpr0.Int, _) ->
        let coef op c1 c2 =
          if op = Texpr0.Add then coeff_add c1 c2
          else coeff_add c1 (Coeff.neg c2) in

        let l1, l2 = linexpr e1, linexpr e2 in
        begin match op with
          | Texpr0.Add | Texpr0.Sub ->
            let lres = Linexpr1.make env in
            Linexpr1.set_cst lres
              (coef op (Linexpr1.get_cst l1) (Linexpr1.get_cst l2));

            let vars = ref [] in
            Linexpr1.iter (fun _ c -> vars := c :: !vars) l1;
            Linexpr1.iter (fun _ c -> vars := c :: !vars) l2;
            let vs = List.sort_uniq Stdlib.compare !vars in

            List.iter (fun v ->
                let c1,c2 = Linexpr1.get_coeff l1 v, Linexpr1.get_coeff l2 v in
                Linexpr1.set_coeff lres v (coef op c1 c2);
              ) vs;
            lres

          | _ -> raise Linexpr_failure end
      | _ -> raise Linexpr_failure in

    try Some (linexpr t.mexpr) with Linexpr_failure -> None


  (* We rewrite the expression to perform soundly weak updates *)
  let rec weak_transf is_spec map e =
    match e with
    | Mcst c -> (map, Mcst c)
    | Mvar mvar ->
      if weak_update is_spec mvar then
        let i = Mm.find_default 0 mvar map in
        let map' = Mm.add mvar (i + 1) map in
        (map', Mvar (weak_cp mvar i))
      else (map, Mvar mvar)

    | Munop (op1, a, t, r) ->
      let map',a' = weak_transf is_spec map a in
      (map', Munop (op1, a', t, r))

    | Mbinop (op2, a, b, t, r) ->
      let map',a' = weak_transf is_spec map a in
      let map'',b' = weak_transf is_spec map' b in
      (map'', Mbinop (op2, a', b', t, r))

  let get_var_mexpr e =
    let rec aux acc = function
      | Mcst _ -> acc
      | Mvar mvar -> mvar :: acc
      | Munop (_, a, _, _) -> aux acc a
      | Mbinop (_, a, b, _, _) -> aux (aux acc a) b in
    aux [] e
    |> u8_blast_vars ~blast_arrays:true
    |> List.sort_uniq Stdlib.compare

  let rec contains_mod = function
    | Mvar _ | Mcst _ -> false
    | Munop (_, a, _, _) -> contains_mod a
    | Mbinop (op2, a, b, _, _) ->
      (op2 = Texpr0.Mod) || (contains_mod a) || (contains_mod b)

  let extend_environment t apr_env =
    let cmp = Environment.compare t.env apr_env in
    if cmp = -1 || cmp = 0 then
      { t with env = apr_env }
    else begin
      Format.eprintf "@[%a@;%a@]@." pp_apr_env t.env pp_apr_env apr_env;
      raise (Aint_error "The environment is not compatible") end

  let rec equal_mexpr_aux t t' = match t, t' with
    | Mvar v, Mvar v' -> v = v'
    | Mcst c, Mcst c' -> Coeff.equal c c'
    | Munop (op, e, typ, rnd), Munop (op', e', typ', rnd') 
      -> op = op' && typ = typ' && rnd = rnd' && equal_mexpr_aux e e'
    | Mbinop (op, e1, e2, typ, rnd), Mbinop (op', e1', e2', typ', rnd') 
      -> op = op' && typ = typ' && rnd = rnd' 
         && equal_mexpr_aux e1 e1'
         && equal_mexpr_aux e2 e2'
    | _ -> false

  let equal_mexpr t t' = equal_mexpr_aux t.mexpr t'.mexpr
end


(******************)
(* Tcons1 Wrapper *)
(******************)

module Mtcons : sig
  type t
  type typ = Apron.Lincons0.typ

  val make : Mtexpr.t -> typ -> t

  val to_atcons : t -> Tcons1.t
  val to_lincons : t -> apr_env -> Lincons1.t option

  val get_expr : t -> Mtexpr.t
  val get_typ : t -> typ

  (* This does not check equality of the underlying Apron environments. *)
  val equal_tcons : t -> t -> bool

  val print : Format.formatter -> t -> unit
  val print_mexpr : Format.formatter -> t -> unit
end = struct
  type typ = Apron.Lincons0.typ

  type t = { expr : Mtexpr.t;
             typ : typ }

  let make t ty = { expr = t; typ = ty }

  let to_atcons t = Tcons1.make (Mtexpr.to_aexpr t.expr) t.typ

  let to_lincons t env =
    omap (fun linexpr -> Lincons1.make linexpr t.typ)
      (Mtexpr.to_linexpr t.expr env)

  let get_expr t = t.expr
  let get_typ t = t.typ

  let equal_tcons t t' =
    Mtexpr.equal_mexpr t.expr t'.expr
    && t.typ = t'.typ

  let print ppf t = to_atcons t |> Tcons1.print ppf

  (* for debugging *)
  let print_mexpr ppf t = 
    Format.fprintf ppf "%a %s 0" 
      Mtexpr.print_mexpr t.expr.mexpr
      (Lincons1.string_of_typ t.typ)
end


(**************)
(* More Utils *)
(**************)

let cst_of_mpqf apr_env n =
  Mtexpr.cst apr_env (Coeff.s_of_mpqf n)

(* Return the texpr 2^n - y *)
let cst_pow_minus apr_env n y =
  mpq_pow_minus n y
  |> cst_of_mpqf apr_env



(***********************)
(* Analyzer parameters *)
(***********************)

type analyzer_param = { relationals : string list option;
                        pointers : string list option }


(**********************)
(* Generic Thresholds *)
(**********************)

let int_thresholds =
  (* For unsigned *)
  List.map (fun i -> mpq_pow_minus i 1) [8;16;32;64;128;256]
  (* (\* For signed *\)
   * @ List.map (fun i -> mpq_pow_minus i 1) [7;15;31;63;127;255]
   * @ List.map (fun i -> mpq_pow_minus i 0) [7;15;31;63;127;255] *)

let neg i = Mpqf.neg i


let lcons env v i vneg iminus =
  let e = Linexpr1.make env in
  let ci = Coeff.s_of_mpqf (if iminus then neg i else i)
  and cv = Coeff.s_of_int (if vneg then -1 else 1) in
  let () = Linexpr1.set_list e [cv,v] (Some ci) in
  e

(* Makes the bounds 'v >= 0' and 'v <= 2^N-1' for 'N' in {8;16;32;64;128;256} *)
let thresholds_uint env v =
  let acc = 
    [Lincons1.make (lcons env v (Mpqf.of_int 0) false true) Lincons0.SUPEQ] in
  List.fold_left (fun acc i ->
      let lc = lcons env v i in
      Lincons1.make (lc true false) Lincons0.SUPEQ :: acc
    ) acc int_thresholds

(* FIXME: rename *)
let thresholds_zero env =
  let vars = Environment.vars env
             |> fst
             |> Array.to_list in
    List.fold_left (fun thrs v -> thresholds_uint env v @ thrs
    ) [] vars

  (* List.map (fun v ->
   *     Lincons1.make (lcons env v (Mpqf.of_int 0) false true) Lincons0.SUPEQ
   *   ) vars *)
    
let thresholds_vars env =
  let vars = Environment.vars env
             |> fst
             |> Array.to_list in

  List.fold_left (fun acc v ->
      List.fold_left (fun acc i ->
          let lc = lcons env v i in
          (Lincons1.make (lc true true) Lincons0.SUPEQ)
          :: (Lincons1.make (lc true false) Lincons0.SUPEQ)
          :: (Lincons1.make (lc false true) Lincons0.SUPEQ)
          :: (Lincons1.make (lc false false) Lincons0.SUPEQ)
          :: acc) acc int_thresholds)
    [] vars


let thresholds_param env param =
  let param_pts  = Utils.odfl [] param.pointers
  and param_rels = Utils.odfl [] param.relationals  in

  let vars = fst (Environment.vars env)
             |> Array.to_list in
  
  let param_rels = List.filter_map (fun v -> match mvar_of_avar v with
      | MinValue gv ->
        if List.mem gv.v_name param_rels then Some v else None
      | _ -> None) vars in
  
  let thrs_v v =
    List.map (fun inv ->
        let e = Linexpr1.make env in
        let cv, cinv = Coeff.s_of_int (-1), Coeff.s_of_int 1 in
        let c0 = Coeff.s_of_int 0 in
        let () = Linexpr1.set_list e [(cv,v);(cinv,inv)] (Some c0) in
        Lincons1.make e Lincons0.SUPEQ
      ) param_rels in
                
  List.fold_left (fun thrs v ->
      match mvar_of_avar v with
      | MmemRange (MemLoc gv) ->
        if List.mem gv.v_name param_pts
        then thrs_v v @ thrs
        else thrs
      | _ -> thrs
    ) [] vars


(************************************)
(* Numerical Domain Pretty Printing *)
(************************************)

module type AprManager = sig
  type t

  val man : t Apron.Manager.t
end

module PP (Man : AprManager) : sig
  val pp : Format.formatter -> Man.t Apron.Abstract1.t -> unit
end = struct
  let coeff_eq_1 (c: Coeff.t) = match c with
    | Coeff.Scalar s when Scalar.cmp_int s 1 = 0 -> true
    | Coeff.Interval i when
        Scalar.cmp_int i.Interval.inf 1 = 0 &&
        Scalar.cmp_int i.Interval.sup 1 = 0 -> true
    | _ -> false

  let coeff_eq_0 (c: Coeff.t) = match c with
    | Coeff.Scalar s -> Scalar.cmp_int s 0 = 0
    | Coeff.Interval i ->
      Scalar.cmp_int i.Interval.inf 0 = 0
      && Scalar.cmp_int i.Interval.sup 0 = 0

  let coeff_cmp_0 (c: Coeff.t) = match c with
    | Coeff.Scalar s -> Some (Scalar.cmp_int s 0)
    | Coeff.Interval i ->
      if Scalar.cmp_int i.Interval.inf 0 > 0 then Some 1
      else if Scalar.cmp_int i.Interval.sup 0 < 0 then Some (-1)
      else None

  let pp_coef_var_list fmt l =
    match l with
    | [] -> Format.fprintf fmt "0"
    | _ -> Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " + ")
             (fun fmt (c, v) ->
                if coeff_eq_1 c then
                  Format.fprintf fmt "%s" (Var.to_string v)
                else
                  Format.fprintf fmt "%a·%s" Coeff.print c (Var.to_string v)) fmt l

  let pp_typ fmt (x, b) = match x, b with
    | Lincons1.DISEQ, _ -> Format.fprintf fmt "!="
    | Lincons1.EQ, _ -> Format.fprintf fmt "="
    | Lincons1.SUP, false -> Format.fprintf fmt ">"
    | Lincons1.SUP, true -> Format.fprintf fmt "<"
    | Lincons1.SUPEQ, false -> Format.fprintf fmt "≥"
    | Lincons1.SUPEQ, true -> Format.fprintf fmt "≤"
    | Lincons1.EQMOD _, _ -> assert false

  let neg_list l =
    List.map (fun (c, v) -> Coeff.neg c, v) l

  let linexpr_to_list_pair env (x: Linexpr1.t) =
    let envi, _ = Environment.vars env in
    Array.fold_left (fun (pos, neg) var ->
        let c = Linexpr1.get_coeff x var in
        if coeff_eq_0 c then (pos, neg)
        else match coeff_cmp_0 c with
          | None -> (c, var) :: pos, neg
          | Some x when x > 0 -> (c, var) :: pos, neg
          | Some _ -> pos, (c, var)::neg
      ) ([], []) envi

  let pp_lincons fmt lc =
    let cst = Lincons1.get_cst lc in
    let typ = Lincons1.get_typ lc in
    let pos, neg =
      linexpr_to_list_pair (Lincons1.get_env lc) (Lincons1.get_linexpr1 lc) in
    if coeff_eq_0 (cst) then
      Format.fprintf fmt "%a %a %a"
        pp_coef_var_list pos
        pp_typ (typ, false)
        pp_coef_var_list (neg_list neg)
    else
      match coeff_cmp_0 (cst) with
      | Some x when x > 0 ->
        if pos = [] then
          Format.fprintf fmt "%a %a %a"
            pp_coef_var_list (neg_list neg)
            pp_typ (typ, true)
            Coeff.print cst
        else if neg = [] then
          Format.fprintf fmt "%a %a %a"
            pp_coef_var_list pos pp_typ
            (typ, false)
            Coeff.print (Coeff.neg cst)
        else 
          Format.fprintf fmt "%a %a %a + %a"
            pp_coef_var_list (neg_list neg)
            pp_typ (typ, true) pp_coef_var_list pos Coeff.print cst
      | _ ->
        if neg = [] then
          Format.fprintf fmt "%a %a %a"
            pp_coef_var_list pos pp_typ (typ, false)
            Coeff.print (Coeff.neg cst)
        else if pos = [] then
          Format.fprintf fmt "%a %a %a" pp_coef_var_list (neg_list neg)
            pp_typ (typ, true) Coeff.print (cst)
        else 
          Format.fprintf fmt "%a %a %a + %a" pp_coef_var_list pos
            pp_typ (typ, false) pp_coef_var_list (neg_list neg)
            Coeff.print (Coeff.neg cst)

  let pp_lincons_earray fmt ea =
    let rec read n =
      if n < 0 then []
      else
        let x = Lincons1.array_get ea n in
        x :: (read (n-1))
    in
    let l = read (Lincons1.array_length ea -1) in
    match l with
    | [] -> Format.fprintf fmt "⊤"
    | _ -> 
      Format.fprintf fmt "{%a}"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
                                   pp_lincons) l


  let pp fmt x =
    let man = Man.man in
    if Abstract1.is_bottom man x then
      Format.fprintf fmt "⊥"
    else
      let ea = Abstract1.to_lincons_array man x in
      pp_lincons_earray fmt ea
end

(*******************)
(* Abstract Values *)
(*******************)

module BoxManager : AprManager with type t = Box.t = struct
  type t = Box.t

  let man = Box.manager_alloc ()
end

module OctManager : AprManager = struct
  type t = Oct.t

  let man = Oct.manager_alloc ()
end

module PplManager : AprManager = struct
  type t = Ppl.strict Ppl.t

  let man = Ppl.manager_alloc_strict ()
end

module type AbsNumType = sig
  type t

  (* C.f. AbsBoolNoRel desciption *)
  val init_is_spec : bool -> unit

  (* Make a top value defined on the given variables *)
  val make : mvar list -> t

  val meet : t -> t -> t
  val meet_list : t list -> t

  val join : t -> t -> t
  val join_list : t list -> t

  (* Because we do not have a backward analysis, we can give the loop condition
     to the widening, which uses it as threshold. *)
  val widening : Mtcons.t option -> t -> t -> t

  val forget_list : t -> mvar list -> t

  val is_included : t -> t -> bool
  val is_bottom : t -> bool
  val bottom : t -> t
  val top : t -> t

  (* expand t v v_list : v and v_list cannot contain Mvalue (AarrayEl)
     elements *)
  val expand : t -> mvar -> mvar list -> t
  (* fold t v_list : v_list cannot contain Mvalue (AarrayEl)
     elements *)
  val fold : t -> mvar list -> t

  val bound_variable : t -> mvar -> Interval.t
  val bound_texpr : t -> Mtexpr.t -> Interval.t

  val assign_expr : ?force:bool -> t -> mvar -> Mtexpr.t -> t

  val meet_constr : t -> Mtcons.t -> t
  val meet_constr_list : t -> Mtcons.t list -> t

  (* Unify the two abstract values on their least common environment. *)
  val unify : t -> t -> t

  (* Variables that are removed are first existentially quantified, and
     variables that are introduced are unconstrained. *)
  val change_environment : t -> mvar list -> t
  val remove_vars : t -> mvar list -> t

  val to_box : t -> Box.t Abstract1.t
  val of_box : Box.t Abstract1.t -> t

  val get_env : t -> Environment.t

  val print : ?full:bool -> Format.formatter -> t -> unit
end


module type ProgWrap = sig
  val main : unit Prog.func
  val prog : unit Prog.prog
  val param : analyzer_param
end

module AbsNumI (Manager : AprManager) (PW : ProgWrap) : AbsNumType = struct

  type t = Manager.t Abstract1.t
  let man = Manager.man

  let v_is_spec = ref None 
  let init_is_spec b = match !v_is_spec with
    | None -> v_is_spec := Some b
    | Some _ -> assert false    (* Should not initialize this twice *)

  let is_spec () = oget !v_is_spec

  let is_relational () = Ppl.manager_is_ppl man

  let make l =
    let vars = u8_blast_vars ~blast_arrays:true l |>
               List.map avar_of_mvar |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let env = Environment.make vars empty_var_array in
    Abstract1.top man env

  let lce a a' =
    let lce = Environment.lce (Abstract1.env a) (Abstract1.env a') in
    (Abstract1.change_environment man a lce false,
     Abstract1.change_environment man a' lce false)

  let env_lce l =
    if l = [] then raise (Aint_error "Lce of an empty list");
    List.fold_left Environment.lce (List.hd l) l

  let lce_list l =
    if l = [] then raise (Aint_error "Lce of an empty list");
    let lce = List.map Abstract1.env l |> env_lce in
    List.map (fun a -> Abstract1.change_environment man a lce false) l

  let meet a a' =
    let a,a' = lce a a' in
    Abstract1.meet man a a'

  let meet_list a_list =
    if a_list = [] then raise (Aint_error "Meet of an empty list");
    let a_list = lce_list a_list in
    Abstract1.meet_array man (Array.of_list a_list)

  let join a a' =
    let a,a' = lce a a' in
    Abstract1.join man a a'

  let join_list a_list =
    if a_list = [] then raise (Aint_error "Join of an empty list");
    let a_list = lce_list a_list in
    Abstract1.join_array man (Array.of_list a_list)

  let earray_to_list ea = 
    List.init
      (Lincons1.array_length ea)
      (fun i -> Lincons1.array_get ea i)
    
  let to_earray env l =
    let arr = Lincons1.array_make env (List.length l) in
    let () = List.iteri (fun i c -> Lincons1.array_set arr i c) l in
    arr

  let thrs_of_oc oc env =
    match omap_dfl (fun x -> Mtcons.to_lincons x env) None oc with
    | None -> []
    | Some lc -> [lc]

  (* let enrich_widening a a' res =
   *   let env = Abstract1.env a in
   *   let ea = Abstract1.to_lincons_array man a
   *            |> earray_to_list in
   *   let to_add = List.filter (fun lin -> Abstract1.sat_lincons man a' lin) ea
   *                |> to_earray env in
   *   Abstract1.meet_lincons_array man res to_add *)

  let compute_thresholds env oc =
    let vars = omap_dfl (fun c -> 
        Mtexpr.get_var_mexpr (Mtcons.get_expr c).mexpr
      ) [] oc in
    let thrs_vars = 
      List.map (fun v -> thresholds_uint env (avar_of_mvar v)) vars 
      |> List.flatten in
    let thrs_oc = thrs_of_oc oc env in
    let thrs = thrs_oc @ thrs_vars in
    let thrs =
      if Aparam.more_threshold then thresholds_vars env @ thrs else thrs in
    let thrs =
      if Aparam.zero_threshold then thresholds_zero env @ thrs else thrs in
    let thrs =
      if Aparam.param_threshold
      then thresholds_param env PW.param @ thrs
      else thrs in

    if is_relational () then
      debug(fun () -> Format.eprintf "@[<v 2>threshold(s):@; %a@."
               (pp_list Lincons1.print) thrs);
    thrs

  let widening oc a a' =
    let a,a' = lce a a' in
    let env = Abstract1.env a in
    
    let thrs = compute_thresholds env oc in
    
    (* Be careful to join a and a' before calling widening. Some abstract domain,
       e.g. Polka, seem to assume that a is included in a'
       (and may segfault otherwise!). *)
    let res = Abstract1.widening_threshold man a a' (thrs |> to_earray env) in
    (* if Aparam.enrich_widening
     * then enrich_widening a a' res
     * else  *)res

  let forget_list a l =
    let l = u8_blast_vars ~blast_arrays:true l in
    let env = Abstract1.env a in
    let al = List.filter
        (Environment.mem_var env) (List.map avar_of_mvar l) in
    Abstract1.forget_array man a (Array.of_list al) false

  let is_included a a' =
    let a,a' = lce a a' in
    Abstract1.is_leq man a a'

  let is_bottom a = Abstract1.is_bottom man a

  let bottom_man man a = Abstract1.bottom man (Abstract1.env a)
  let bottom = bottom_man man

  let top_man man a = Abstract1.top man (Abstract1.env a)
  let top = top_man man

  let check_u8 vs =
    assert (List.for_all (function
        | Mvalue (AarrayEl (_,ws,_)) -> ws = U8
        | _ -> true) vs)
      
  (* v and v_list should not contain Mvalue (AarrayEl) elements
     of size different than U8. *)
  let expand_man man a v v_list =
    check_u8 (v :: v_list);
    let v_array = Array.of_list (List.map avar_of_mvar v_list) in
    Abstract1.expand man a (avar_of_mvar v) v_array

  (* v_list should not contain Mvalue (AarrayEl) elements
     of size different than U8. *)
  let fold_man man a v_list =
    check_u8 (v_list);
    (* PPL implementation of the fold operation is bugged. *)   
    (* let v_array = Array.of_list (List.map avar_of_mvar v_list) in 
     * Abstract1.fold man a v_array *)

    (* We do it instead using assignments and joins. *)
    let v, vs = match List.map avar_of_mvar v_list with
      | v :: vs -> v, vs
      | [] -> raise (Failure "fold_man: empty list") in
    let env = Abstract1.env a in
    
    let ass = List.map (fun v' ->
        let ev' = Texpr1.of_expr env (Texpr1.Var v') in
        Abstract1.assign_texpr man a v ev' None) vs in
    let arr = Array.of_list (a :: ass) in
    let a = Abstract1.join_array man arr in

    (* We remove the variables [vs]. *)
    let vars = Environment.vars env
               |> fst
               |> Array.to_list in
    let nvars = List.filter (fun x -> not (List.mem x vs)) vars
                |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in

    let new_env = Environment.make nvars empty_var_array in
    Abstract1.change_environment man a new_env false

  
  let expand a v v_list = expand_man man a v v_list

  let fold a v_list = fold_man man a v_list

  let add_weak_cp_man man a map =
    Mm.fold (fun v i a ->
        let vs = List.init i (Mtexpr.weak_cp v) in
        expand_man man a v vs) map a

  let rem_weak_cp_man man a map =
    Mm.fold (fun v i a ->
        let vs = List.init i (Mtexpr.weak_cp v) in
        fold_man man a (v :: vs)) map a

  let add_weak_cp = add_weak_cp_man man

  let rem_weak_cp = rem_weak_cp_man man

  let prepare_env env mexpr =
    let vars_mexpr =
      List.map avar_of_mvar (Mtexpr.get_var_mexpr mexpr) |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let env_mexpr = Environment.make vars_mexpr empty_var_array in
    Environment.lce env env_mexpr

  let bound_texpr_man man a (e : Mtexpr.t) =
    (* We use a different variable for each occurrence of weak variables *)
    let map,mexpr = Mtexpr.weak_transf (is_spec ()) Mm.empty e.mexpr in
    let a = add_weak_cp_man man a map in

    let env = prepare_env (Abstract1.env a) e.mexpr in
    let a = Abstract1.change_environment man a env false in
    let e' = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                               Mtexpr.env = env } in

    Abstract1.bound_texpr man a e'

  let bound_texpr = bound_texpr_man man

  let bound_variable t v = match v with
    | Mvalue (AarrayEl _) ->
      let env = Abstract1.env t in
      bound_texpr t (Mtexpr.var env v)
    | _ -> Abstract1.bound_variable man t (avar_of_mvar v)

  let env_add_mvar env v =
    let add_single v env =
      let av = avar_of_mvar v in
      if Environment.mem_var env av then env
      else
        Environment.add env
          (Array.of_list [av])
          (Array.make 0 (Var.of_string "")) in

    match v with
    (* | Mvalue (Avar at) | MvarOffset at ->
     *   add_single (Mvalue (Avar at)) env
     *   |> add_single (MvarOffset at) *)

    | Mvalue (AarrayEl _ ) ->
      List.fold_left
        (fun x y -> add_single y x) env
        (u8_blast_var ~blast_arrays:true v)

    | _ -> add_single v env

  (* Relational assignment. *)
  let assign_expr_rel force a v e =
    (* We use a different variable for each occurrence of weak variables *)
    let map,mexpr = Mtexpr.weak_transf (is_spec ()) Mm.empty Mtexpr.(e.mexpr) in

    let a = add_weak_cp a map in
    (* We do the same for the variable receiving the assignment *)
    let v_weak = weak_update (is_spec ()) v && not force in
    let a,v_cp = if v_weak then
        let v_cp = Temp ("weaklv_" ^ string_of_mvar v,0, ty_mvar v) in
        (expand a v [v_cp], v_cp)
      else (a, v) in
    (* If v is not in the environment, we add it *)
    let env = env_add_mvar (Abstract1.env a) v_cp in

    (* We add the variables in mexpr to the environment *)
    let env = prepare_env env mexpr in
    let a = Abstract1.change_environment man a env false in
    let e' = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                               Mtexpr.env = env } in

    let a = Abstract1.assign_texpr man a (avar_of_mvar v_cp) e' None in

    (* We fold back the added variables *)
    let a = rem_weak_cp a map in
    if v_weak then fold a [v; v_cp] else a


  (* Forced non relational assignment *)
  let assign_expr_norel force a v e =
    (* We do a copy of v if we do a weak assignment *)
    let v_weak = weak_update (is_spec ()) v && not force in
    let a,v_cp = if v_weak then
        let v_cp = Temp ("weaklv_" ^ string_of_mvar v,0, ty_mvar v) in
        (expand a v [v_cp], v_cp)
      else (a, v) in

    (* If v is not in the environment, we add it *)
    let env = env_add_mvar (Abstract1.env a) v_cp in
    let a = Abstract1.change_environment man a env false in

    let int = Coeff.Interval (bound_texpr a e) in
    let eint = Texpr1.cst env int in

    let a = Abstract1.assign_texpr man a (avar_of_mvar v_cp) eint None in

    (* We fold back v, if needed *)
    if v_weak then fold a [v; v_cp] else a

  let e_complex e =
    (is_relational ()) && (Mtexpr.contains_mod Mtexpr.(e.mexpr))

  let es_complex es = List.exists e_complex es

  (* If the domain is relational, and if e contains a modulo, then we just
     return the interval of variations of e (i.e. we forget all relations
     between v_cp and the other variables). *)
  let assign_expr_aux force a v e =
    if e_complex e then
      assign_expr_norel force a v e
    else assign_expr_rel force a v e


  (* Return the j-th term of the expression e seen in base b = 2^8:
     ((e - (e mod b^j)) / b^j) mod b *)
  let get_block e j =
    let bj = mpq_pow (8 * j) |> Mpqf.of_mpq |> cst_of_mpqf Mtexpr.(e.env)
    and b = mpq_pow 8 |> Mpqf.of_mpq |> cst_of_mpqf Mtexpr.(e.env) in
    (* e - (e mod b^j) *)
    let e1 = Mtexpr.binop Texpr1.Sub e (Mtexpr.binop Texpr1.Mod e bj ) in
    (* e1 / b^j) mod b *)
    Mtexpr.binop Texpr1.Mod ( Mtexpr.binop Texpr1.Div e1 bj) b

  (* If force is true then we do a forced strong update on v. *)
  let assign_expr ?force:(force=false) a v e = match v with
    | Mvalue (AarrayEl (gv,ws,i)) ->
      let offset = (int_of_ws ws) / 8 * i in
      List.fold_left (fun a j ->
          let p = offset + j in
          let mvj = Mvalue (AarrayEl (gv, U8, p)) in
          let mej = get_block e j in
          assign_expr_aux force a mvj mej)
        a (List.init ((int_of_ws ws) / 8) (fun j -> j))

    | _ -> assign_expr_aux force a v e

  module PP = PP(Manager)
      
  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt a ->
      if full && (is_relational ()) then
        Format.fprintf fmt "@[<v 0>@[%a@]@;@]"
          PP.pp a
      (* Abstract1.print a *)
      ;

      let (arr_vars, _) = Environment.vars (Abstract1.env a) in
      let vars = Array.to_list arr_vars in

      let pp_abs fmt v =
        let vi = Abstract1.bound_variable man a v in
        Format.fprintf fmt "@[%s ∊ %a@]"
          (Var.to_string v)
          Interval.print vi in

      let pp_sep fmt () = Format.fprintf fmt "@;" in

      let vars_p = List.filter (fun v ->
          (not Aparam.ignore_unconstrained ||
           (not !Aparam.nrel_no_print || is_relational ()) &&
           not (Abstract1.is_variable_unconstrained man a v)) &&
          not (variables_ignore v)) vars in

      if vars_p <> [] then
        Format.fprintf fmt "@[<v 0>%a@]" (pp_list ~sep:pp_sep pp_abs) vars_p
      else ()

  (* Precond: env is not empty
     (Box1 seems to not behave correctly on empty env) *)
  let to_box1 : 'a Abstract1.t -> Abstract1.box1 = fun a ->
    let vars,_ = Environment.vars (Abstract1.env a) in
    assert (Array.length vars <> 0);
    Abstract1.to_box man a

  (* Precond: env is not empty
     (Box1 seems to not behave correctly on empty env) *)
  let box1_to_box : Abstract1.box1 -> Box.t Abstract1.t = fun box ->
    let env = box.box1_env in
    let vars,_ = Environment.vars env in
    let bman = BoxManager.man in
    assert (Array.length vars <> 0);
    Abstract1.of_box bman env vars Abstract1.(box.interval_array)
        
  let top_box env = 
    let bman = BoxManager.man in
    Abstract1.top bman env

  let bottom_box env = 
    let bman = BoxManager.man in
    Abstract1.bottom bman env

  let to_box :  t -> Box.t Abstract1.t = fun a ->
    (* We do this because box1 does not behave correctly on empty env *)
    if Abstract1.is_top man a then 
      top_box (Abstract1.env a)
    else if Abstract1.is_bottom man a then 
      bottom_box (Abstract1.env a)
    else to_box1 a |> box1_to_box

  (* Precond: env is not empty
     (Box1 seems to not behave correctly on empty env) *)
  let of_box1 (box : Abstract1.box1) =
    let env = box.box1_env in
    let vars,_ = Environment.vars env in
    assert (Array.length vars <> 0);
    Abstract1.of_box man env vars Abstract1.(box.interval_array)

  let of_box : Box.t Abstract1.t -> t = fun a ->
    let bman = BoxManager.man in 
    if Abstract1.is_top bman a then 
      Abstract1.top man (Abstract1.env a)
    else if Abstract1.is_bottom bman a then 
      Abstract1.bottom man (Abstract1.env a)
    else
      Abstract1.to_box bman a |> of_box1

  let trivially_false man a c =
    let int = bound_texpr_man man a (Mtcons.get_expr c) in
    let oi = interval_to_int int in

    Utils.omap_dfl (fun i -> match Mtcons.get_typ c with
        | Tcons0.DISEQ -> i = 0
        | Tcons0.EQ -> i <> 0
        | Tcons0.SUP -> i <= 0
        | Tcons0.SUPEQ -> i < 0
        | Tcons0.EQMOD n -> match scalar_to_int n with
          | None -> false
          | Some n -> (i mod n) <> 0
      ) false oi

  let meet_constr_man man a cs =
    let cs = List.filter (fun c -> not (trivially_false man a c)) cs in
    if cs = [] then bottom_man man a
    else
      let map,cs = List.fold_left (fun (map, acc) c ->
          let e = Mtcons.get_expr c in

          (* We use a different variable for each occurrence of weak variables *)
          let map,mexpr = Mtexpr.weak_transf (is_spec ()) map e.mexpr in

          (* We prepare the expression *)
          let env = prepare_env (Abstract1.env a) mexpr in
          let ae = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                                     Mtexpr.env = env } in
          let c = Tcons1.make ae (Mtcons.get_typ c) in
          (map, c :: acc)
        ) (Mm.empty,[]) cs in

      let a = add_weak_cp_man man a map in
      let env = List.map Tcons1.get_env cs |> env_lce in

      (* We evaluate the constraint *)
      let c_array = Tcons1.array_make env (List.length cs) in
      List.iteri (fun i c -> Tcons1.array_set c_array i c) cs;

      let a = Abstract1.change_environment man a env false in
      let a = Abstract1.meet_tcons_array man a c_array in

      (* We fold back the added variables *)
      rem_weak_cp_man man a map

  let meet_constr_norel a cs =
    let bman = BoxManager.man in
    let ac = meet_constr_man bman (to_box a) cs
             |> of_box in
    meet a ac

  let meet_constr_list a cs =
    let es = List.map Mtcons.get_expr cs in
    if es_complex es then meet_constr_norel a cs
    else meet_constr_man man a cs

  let meet_constr a c = meet_constr_list a [c]

  let unify a a' = Abstract1.unify man a a'

  let change_environment a mvars =
    let env_vars = u8_blast_vars ~blast_arrays:true mvars
                   |> List.map avar_of_mvar
                   |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let new_env = Environment.make env_vars empty_var_array in
    Abstract1.change_environment man a new_env false

  let remove_vars a mvars =
    let vars = Environment.vars (Abstract1.env a)
               |> fst
               |> Array.to_list
    and rem_vars = u8_blast_vars ~blast_arrays:true mvars
                   |> List.map avar_of_mvar  in

    let nvars = List.filter (fun x -> not (List.mem x rem_vars)) vars
                |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in

    let new_env = Environment.make nvars empty_var_array in
    Abstract1.change_environment man a new_env false

  let get_env a = Abstract1.env a

end


(*******************)
(* Domains Product *)
(*******************)

type v_dom = Nrd of int | Ppl of int

let string_of_dom = function
  | Nrd i -> "Nrd" ^ string_of_int i
  | Ppl i -> "Ppl" ^ string_of_int i

module Mdom = Map.Make(struct
    type t = v_dom

    let compare = Stdlib.compare
    let equal u v = u = v
  end)

let is_prefix u v =
  if String.length u <= String.length v then
    String.sub v 0 (String.length u) = u
  else false

module type VDomWrap = sig
  (* Associate a domain (ppl or non-relational) to every variable.
     An array element must have the same domain that its blasted component. *)
  val vdom : mvar -> v_dom

  (* C.f. AbsBoolNoRel desciption *)
  val init_is_spec : bool -> unit
end


(*---------------------------------------------------------------*)
(* Fix-point computation *)
let rec fpt f eq x =
  let x' = f x in
  if (eq x x') then
    x
  else
    fpt f eq x'

module Scmp = struct
  type t = string
  let compare = compare
end

module Ms = Map.Make(Scmp)

(* For now we fixed the domains, and we use only two of them, one non-relational
   and one Ppl. Still, we generalized to n different domains whenever possible
   to help future possible extentions. *)
module AbsNumProd (VDW : VDomWrap) (NonRel : AbsNumType) (PplDom : AbsNumType)
  : AbsNumType = struct

  type t = { nrd : NonRel.t Mdom.t;
             ppl : PplDom.t Mdom.t }

  let is_spec = ref None 
  let init_is_spec b = match !is_spec with
    | None -> is_spec := Some b; NonRel.init_is_spec b; PplDom.init_is_spec b
    | Some _ -> assert false    (* Should not initialize this twice *)

  let nrddoms = [Nrd 0]
  let ppldoms = [Ppl 0]

  (* We need log the result of VDW.vdom for the of_box function. This is not
     clean, but I do not see a simpler way. *)
  let log_index = Hashtbl.create ~random:false 16
  let log = Hashtbl.create ~random:false 16

  let vdom v =
    let r =
      if v= dummy_mvar then Ppl 0 
      else VDW.vdom v in
    let vs = avar_of_mvar v |> Var.to_string in
    (* We also need to add the blasted component of [t] to the log. *)
    let vs_blasted = u8_blast_var ~blast_arrays:false v 
                     |> List.map (fun v -> avar_of_mvar v
                                            |> Var.to_string) in

    let add_to_log vs =
      if not (Hashtbl.mem log_index vs) then begin
        Hashtbl.add log_index vs ();
        Hashtbl.add log r vs
      end in
    List.iter add_to_log (vs :: vs_blasted);
    r

  let pp_dom fmt = function
    | Ppl i -> Format.fprintf fmt "Ppl %d" i
    | Nrd i -> Format.fprintf fmt "Nrd %d" i

  let pp_log fmt () =
    Format.fprintf fmt "@[<v 0>";
    Hashtbl.iter (fun dom v ->
        Format.fprintf fmt "%s --> %a@;" v pp_dom dom)
      log;
    Format.fprintf fmt "@;@]@.";;

  let expr_doms e =
    let rec aux acc = function
      | Mtexpr.Mcst _ -> acc
      | Mtexpr.Mvar v ->
        if List.mem (vdom v) acc then acc else (vdom v) :: acc
      | Mtexpr.Munop (_, e1, _, _) -> aux acc e1
      | Mtexpr.Mbinop (_, e1, e2, _, _) -> aux (aux acc e1) e2 in

    aux [] e

  (* Replace all variables not in domain d by an interval *)
  let proj_expr a d (e : Mtexpr.t) =
    let env = e.env in
    let m_make e = Mtexpr.({ mexpr = e; env = env }) in

    let rec proj_mexpr (e : Mtexpr.mexpr) = match expr_doms e with
      | [] -> m_make e
      | [d'] ->
        if d = d' then m_make e
        else
          let int = match d' with
            | Nrd _ -> NonRel.bound_texpr (Mdom.find d' a.nrd) (m_make e)
            | Ppl _ -> PplDom.bound_texpr (Mdom.find d' a.ppl) (m_make e) in
          Mtexpr.cst env (Coeff.Interval int)

      | _ -> match e with
        | Mtexpr.Munop (op, e1, _, _) -> Mtexpr.unop op (proj_mexpr e1)
        | Mtexpr.Mbinop (op, e1, e2, _, _) ->
          Mtexpr.binop op (proj_mexpr e1) (proj_mexpr e2)
        | _ -> assert false in

    proj_mexpr e.mexpr

  let proj_constr a d (c : Mtcons.t) =
    Mtcons.make (proj_expr a d (Mtcons.get_expr c)) (Mtcons.get_typ c)

  let split_doms l =
    let rec aux (ores,pres) = function
      | [] -> (ores, pres)
      | v :: tail ->
        let res' = match vdom v with
          | Ppl _ as d ->
            if List.mem_assoc d pres then
              (ores, assoc_up d (fun x -> v :: x) pres)
            else
              (ores, (d,[v]) :: pres)

          | Nrd _ as d ->
            if List.mem_assoc d ores then
              (assoc_up d (fun x -> v :: x) ores, pres)
            else
              ((d,[v]) :: ores, pres) in

        aux res' tail in

    aux (List.map (fun d -> (d,[])) nrddoms,
         List.map (fun d -> (d,[])) ppldoms) l

  let make l =
    let (ores,pres) = split_doms l in
    let a = { nrd = Mdom.empty; ppl = Mdom.empty } in

    let a = List.fold_left (fun a (d,lvs) ->
        { a with nrd = Mdom.add d (NonRel.make lvs) a.nrd })
        a ores in

    List.fold_left (fun a (d,lvs) ->
        { a with ppl = Mdom.add d (PplDom.make lvs) a.ppl })
      a pres

  let un_app fnrd fppl a =
    { nrd = Mdom.mapi fnrd a.nrd;
      ppl = Mdom.mapi fppl a.ppl }

  let bin_app fnrd fppl a a' =
    let f_opt f k u v = match u,v with
      | None, _ | _, None ->
        let s = Printf.sprintf
            "bin_app: Domain %s does not exist" (string_of_dom k) in
        raise (Aint_error s)
      | Some x, Some y -> Some (f x y) in

    { nrd = Mdom.merge (f_opt fnrd) a.nrd a'.nrd;
      ppl = Mdom.merge (f_opt fppl) a.ppl a'.ppl }

  let list_app fnrd fppl (l : t list) =
    match l with
    | [] -> raise (Aint_error "list_app of an empty list");
    | a :: _ ->

      { nrd = Mdom.mapi (fun k _ ->
            let els = List.map (fun x -> Mdom.find k x.nrd) l in
            fnrd els) a.nrd;
        ppl = Mdom.mapi (fun k _ ->
            let els = List.map (fun x -> Mdom.find k x.ppl) l in
            fppl els) a.ppl}

  let meet = bin_app NonRel.meet PplDom.meet

  let meet_list = list_app NonRel.meet_list PplDom.meet_list

  let join = bin_app NonRel.join PplDom.join

  let join_list = list_app NonRel.join_list PplDom.join_list

  let widening oc a a' =
    let fp d = omap_dfl (fun c -> proj_constr a' d c |> some) None oc in
    let nroc  = fp (Nrd 0)
    and pploc = fp (Ppl 0) in
    bin_app (NonRel.widening nroc) (PplDom.widening pploc) a a'

  let forget_list a l =
    let f1 _ x = NonRel.forget_list x l
    and f2 _ x = PplDom.forget_list x l in
    un_app f1 f2 a

  let is_included a a' =
    (Mdom.for_all (fun d t -> NonRel.is_included t (Mdom.find d a'.nrd)) a.nrd)
    &&
    (Mdom.for_all (fun d t -> PplDom.is_included t (Mdom.find d a'.ppl)) a.ppl)

  let is_bottom a =
    assert ((Mdom.cardinal a.nrd) + (Mdom.cardinal a.nrd) <> 0);
    (Mdom.exists (fun _ t -> NonRel.is_bottom t) a.nrd)
    && (Mdom.exists (fun _ t -> PplDom.is_bottom t) a.ppl)

  let bottom a =
    let f1 _ x = NonRel.bottom x
    and f2 _ x = PplDom.bottom x in
    un_app f1 f2 a

  let top a =
    let f1 _ x = NonRel.top x
    and f2 _ x = PplDom.top x in
    un_app f1 f2 a

  let expand a v v_list =
    let f1 d x = if vdom v = d then NonRel.expand x v v_list else x
    and f2 d x = if vdom v = d then PplDom.expand x v v_list else x in
    un_app f1 f2 a

  let fold a v_list = match v_list with
    | [] -> raise (Aint_error "fold of an empty list")
    | v :: _ ->
      let f1 d x = if vdom v = d then NonRel.fold x v_list else x
      and f2 d x = if vdom v = d then PplDom.fold x v_list else x in
      un_app f1 f2 a

  let bound_variable a v = match vdom v with
    | Nrd _ -> NonRel.bound_variable (Mdom.find (vdom v) a.nrd) v
    | Ppl _ -> PplDom.bound_variable (Mdom.find (vdom v) a.ppl) v


  (* This works only if there is only one Ppl domain (Ppl 0). *)
  let bound_texpr a (e : Mtexpr.t) =
    let p_e = proj_expr a (Ppl 0) e in
    PplDom.bound_texpr (Mdom.find (Ppl 0) a.ppl) p_e

  (* If force is true then we do a forced strong update on v. *)
  let assign_expr ?force:(force=false) a v (e : Mtexpr.t) =
    let d = vdom v in
    let p_e = proj_expr a d e in
    match d with
    | Nrd _ ->
      let d_a = Mdom.find d a.nrd in
      let d_a' = NonRel.assign_expr ~force:force d_a v p_e in
      { a with nrd = Mdom.add d d_a' a.nrd }

    | Ppl _ ->
      let d_a = Mdom.find d a.ppl in
      let d_a' = PplDom.assign_expr ~force:force d_a v p_e in
      { a with ppl = Mdom.add d d_a' a.ppl }


  let meet_constr_list a cs =
    let f1 d x = NonRel.meet_constr_list x (List.map (proj_constr a d) cs)
    and f2 d x = PplDom.meet_constr_list x (List.map (proj_constr a d) cs) in
    un_app f1 f2 a

  let meet_constr a c =
    let f1 d x = NonRel.meet_constr x (proj_constr a d c)
    and f2 d x = PplDom.meet_constr x (proj_constr a d c) in
    un_app f1 f2 a

  let unify = bin_app NonRel.unify PplDom.unify

  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt a ->
      let pp_map pp_el fmt l =
        pp_list pp_el fmt (List.map snd (Mdom.bindings l)) in
      
      if Mdom.cardinal a.nrd = 0 || !only_rel_print then
        Format.fprintf fmt "@[<v 0>* Rel:@;%a@]"
          (pp_map (PplDom.print ~full:full)) a.ppl
      else
        let nrd_size = Mdom.fold (fun _ nrd size ->
            size + Environment.size (NonRel.get_env nrd)
          ) a.nrd 0 in
        let ppl_size = Mdom.fold (fun _ nrd size ->
            size + Environment.size (PplDom.get_env nrd)
          ) a.ppl 0 in

        Format.fprintf fmt "@[<v 0>\
                            * NonRel (%d vars.):@;%a\
                            * Rel (%d vars.):@;%a@]"
          nrd_size
          (pp_map (NonRel.print ~full:full)) a.nrd
          ppl_size
          (pp_map (PplDom.print ~full:full)) a.ppl

  let change_environment a mvars =
    let (ores,pres) = split_doms mvars in

    let f1 d x = NonRel.change_environment x (List.assoc d ores)
    and f2 d x = PplDom.change_environment x (List.assoc d pres) in
    un_app f1 f2 a

  let remove_vars a mvars =
    let (ores,pres) = split_doms mvars in

    let f1 d x = NonRel.remove_vars x (List.assoc d ores)
    and f2 d x = PplDom.remove_vars x (List.assoc d pres) in
    un_app f1 f2 a

  let get_env a =
    let l =
      Mdom.fold (fun _ a l ->
          let vars,_ = NonRel.get_env a |> Environment.vars in
          Array.to_list vars @ l) a.nrd []
      |> Mdom.fold (fun _ a l ->
          let vars,_ = PplDom.get_env a |> Environment.vars in
          Array.to_list vars @ l) a.ppl in

    let env_vars = Array.of_list l
    and empty_var_array = Array.make 0 (Var.of_string "") in
    Environment.make env_vars empty_var_array


  let to_box a =
    let env = get_env a in
    let bman = Box.manager_alloc () in
    let l =
      Mdom.fold (fun _ a acc ->
          Abstract1.change_environment bman (NonRel.to_box a) env false
          :: acc
        ) a.nrd []
      |> Mdom.fold (fun _ a acc ->
          Abstract1.change_environment bman (PplDom.to_box a) env false
          :: acc
        ) a.ppl in

    Abstract1.meet_array bman (Array.of_list l)

  (* This is messy because we have to use the log to inverse avar_of_mvar *)
  let of_box (box : Box.t Abstract1.t) =
    let vars = Environment.vars (Abstract1.env box)
               |> fst
               |> Array.to_list
               |> List.map Var.to_string in
    let bman = Box.manager_alloc () in

    let denv dom =
      let dvars = Hashtbl.find_all log dom
                  |> List.filter (fun x -> List.mem x vars)
                  |> List.map Var.of_string
                  |> Array.of_list
      and empty_var_array = Array.make 0 (Var.of_string "") in
      Environment.make dvars empty_var_array in

    let res = List.fold_left (fun a dom ->
        let penv = denv dom in
        let av = Abstract1.change_environment bman box penv false
                 |> NonRel.of_box in
        { a with nrd = Mdom.add dom av a.nrd }
      ) (make []) nrddoms in

    List.fold_left (fun a dom ->
        let penv = denv dom in
        let av = Abstract1.change_environment bman box penv false
                 |> PplDom.of_box in
        { a with ppl = Mdom.add dom av a.ppl }
      ) res ppldoms

end


(*********************)
(* Boolean Variables *)
(*********************)

(* A boolean variable is a positive of negative variable (of type [mvar]). *)
module Bvar : sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool

  (* the boolean is true if t is positive. *)
  val make : mvar -> bool -> t

  val not : t -> t

  val var_name : t -> string

  (* Force the boolean variable to be positive *)
  val positive : t -> t

  val print : Format.formatter -> t -> unit
end = struct
  type t = mvar * bool          (* the boolean is true if t is positive. *)

  let compare (bv,b) (bv',b') = 
    match Stdlib.compare b b' with
    | 0 -> Stdlib.compare (avar_of_mvar bv) (avar_of_mvar bv')
    | _ as r -> r

  let equal (bv,b) (bv',b') = 
    avar_of_mvar bv = avar_of_mvar bv' && b = b'

  let make bv b = (bv,b)

  let not (bv,b) = (bv,not b)

  let positive (bv,_) = (bv,true)

  let var_name (bv,_) = Var.to_string (avar_of_mvar bv)

  let print fmt (bv,b) =
    let v = Var.to_string (avar_of_mvar bv) in
    if b then Format.fprintf fmt "%s" v
    else Format.fprintf fmt "NOT %s" v
end

module Mbv = Map.Make(Bvar)


(***************************************)
(* Boolean combination of constraints. *)
(***************************************)

type btcons =
  | BLeaf of Mtcons.t
  | BVar of Bvar.t
  | BAnd of btcons * btcons
  | BOr of btcons * btcons

let rec pp_btcons ppf = function
  | BLeaf t -> Mtcons.print_mexpr ppf t

  | BVar bv -> Bvar.print ppf bv

  | BAnd (bl,br) ->
    Format.fprintf ppf "(%a@ AND@ %a)"
      pp_btcons bl pp_btcons br

  | BOr (bl,br) ->
    Format.fprintf ppf "(%a@ OR@ %a)"
      pp_btcons bl pp_btcons br

let true_tcons1 env =
  let zero_t = Coeff.s_of_int 0 in
  Mtcons.make (Mtexpr.cst env zero_t) Tcons1.EQ

let false_tcons1 env =
  let zero_t = Coeff.s_of_int 0 in
  Mtcons.make (Mtexpr.cst env zero_t) Tcons1.DISEQ

(* Return the negation of c, except for EQMOD.
   For EQMOD, we return a constraint that always hold. *)
let flip_constr c =
  let t = Mtcons.get_expr c in
  match Mtcons.get_typ c with
  | Tcons1.EQ -> Mtcons.make t Tcons1.DISEQ |> some
  | Tcons1.DISEQ -> Mtcons.make t Tcons1.EQ |> some
  | Tcons1.SUPEQ ->
    let mt = Mtexpr.unop Texpr1.Neg t in
    Mtcons.make mt Tcons1.SUP |> some

  | Tcons1.SUP ->
    let mt = Mtexpr.unop Texpr1.Neg t in
    Mtcons.make mt Tcons1.SUPEQ |> some

  | Tcons1.EQMOD _ -> None (* Remark: For small i, we could do something *)


exception Bop_not_supported

let rec flip_btcons : btcons -> btcons option = fun c ->
  let rec flip_btcons_aux = function
    | BLeaf c -> begin match flip_constr c with
        | Some fc -> BLeaf fc
        | None -> raise Bop_not_supported end
    | BVar bv -> BVar (Bvar.not bv)
    | BAnd (bl,br) -> BOr (flip_btcons_aux bl, flip_btcons_aux br)
    | BOr (bl,br) -> BAnd (flip_btcons_aux bl, flip_btcons_aux br) in

  try Some (flip_btcons_aux c) with Bop_not_supported -> None


(* Type of expression that have been split to remove IfThenElse *)
type s_expr = (btcons list * Mtexpr.t option) list

let sexpr_from_simple_expr : Mtexpr.t -> s_expr = fun expr ->
  [([], Some expr)]

let pp_s_expr fmt (e : s_expr) =
  let pp_el fmt (l,t_opt) =
    Format.fprintf fmt "@[<v 0>%d constraints:@;@[<v 1>%a@]@;term: @[%a@]@]"
      (List.length l)
      (pp_list pp_btcons) l
      (pp_opt Mtexpr.print_mexpr) ((omap (fun x -> Mtexpr.(x.mexpr))) t_opt) in

  Format.fprintf fmt "@[<v 0>%a@]"
    (pp_list pp_el) e


(*************************)
(* Partition Tree Domain *)
(*************************)

type cnstr = { mtcons : Mtcons.t; 
               cpt_uniq : int;
               loc : L.t }

let pp_cnstr fmt c =
  Format.fprintf fmt "(%d) %a: %a"
    (c.cpt_uniq)
    L.pp_sloc c.loc
    Mtcons.print c.mtcons

let pp_cnstrs fmt =
  Format.fprintf fmt "%a"
    (pp_list ~sep:(fun fmt () -> Format.fprintf fmt ";@ ") pp_cnstr)

module Ptree = struct
  (* Trace partitionning, where:
     - [constr] is a constraint, comprising a linear constraint and a 
     program point.
     - [n_true] and [n_false] are abstract states over-approximating traces 
     that went through the constraint, and where it evaluated to, 
     respectively, true and false.  
     - [n_unknwn] over-approximates traces that did not go through the 
     constraint. *)
  type 'a node = { constr   : cnstr;
                n_true   : 'a;
                n_false  : 'a;
                n_unknwn : 'a; }
  
  type 'a t =
    | Node of 'a t node
    | Leaf of 'a


  let rec pp_ptree pp_leaf fmt = function
    | Leaf x -> pp_leaf fmt x
    | Node ({ n_true = Leaf nt;
              n_false = Leaf nf;
              n_unknwn = Leaf nu;} as node) ->
      Format.fprintf fmt "@[<v 0>@[<v 2># @[%a@] :@;\
                          @[%a@]@]@;\
                          @[<v 2># NOT @[%a@] :@;\
                          @[%a@]@]@;\
                          @[<v 2># UNKNOWN @[%a@] :@;\
                          @[%a@]@]@;@]"
        pp_cnstr node.constr
        pp_leaf nt
        pp_cnstr node.constr
        pp_leaf nf
        pp_cnstr node.constr
        pp_leaf nu

    | Node node ->
      Format.fprintf fmt "@[<v 0>\
                          @[<v 2># @[%a@] :@;\
                          @[%a@]@]@;\
                          @[<v 2># NOT @[%a@] :@;\
                          @[%a@]@]@;\
                          @[<v 2># UNKNOWN @[%a@] :@;\
                          @[%a@]@]@;@]"
        pp_cnstr node.constr
        (pp_ptree pp_leaf) node.n_true
        pp_cnstr node.constr
        (pp_ptree pp_leaf) node.n_false
        pp_cnstr node.constr
        (pp_ptree pp_leaf) node.n_unknwn

  let flip c = flip_constr c |> otolist

  let rec same_shape t1 t2 = match t1, t2 with
    | Node n1, Node n2 -> same_shape_n n1 n2
    | Leaf _, Leaf _ -> true
    | _ -> false

  and same_shape_n n1 n2 =
    n1.constr.cpt_uniq = n2.constr.cpt_uniq &&
    same_shape n1.n_true n2.n_true &&
    same_shape n1.n_false n2.n_false &&
    same_shape n1.n_unknwn n2.n_unknwn
    
  let apply (f : 'a -> 'b) (t : 'a t) =
    let rec aux t = match t with
      | Node { constr = c; n_true = nt; n_false = nf; n_unknwn = nu; }
        -> Node { constr   = c;
                  n_true   = aux nt;
                  n_false  = aux nf;
                  n_unknwn = aux nu; } 
      | Leaf x -> Leaf (f x) in
    aux t

    (* let apply (f : Mtcons.t list -> 'a -> 'b) (t : 'a t) =
     * let rec aux cs t = match t with
     *   | Node { constr = c; n_true = nt; n_false = nf; n_unknwn = nu; }
     *     -> Node { constr = c;
     *               n_true = aux (c.mtcons :: cs) nt;
     *               n_false = aux (flip c.mtcons @ cs ) nf;
     *               n_unknwn = nu; } (\* TODO: fixme ! *\)
     *   | Leaf x -> Leaf (f cs x) in
     * aux [] t *)
      
  let apply2_merge (fmerge : 'a t -> 'b t -> ('a t * 'b t))
      (f : 'a -> 'b -> 'c) t1 t2 =
    let rec aux t1 t2 = match t1,t2 with
      | Node { constr = c ; n_true = nt ; n_false = nf ; n_unknwn = nu ; },
        Node { constr = c'; n_true = nt'; n_false = nf'; n_unknwn = nu'; }
        when c.cpt_uniq = c'.cpt_uniq ->
        Node { constr   = c;
               n_true   = aux nt nt';
               n_false  = aux nf nf';
               n_unknwn = aux nu nu'; }

      | Leaf x1, Leaf x2 -> Leaf (f x1 x2)
      | _ -> raise (Aint_error "Ptree: Shape do not match") in

    let t1, t2 = if same_shape t1 t2 then t1,t2 else fmerge t1 t2 in

    aux t1 t2

    (* let apply2_merge (fmerge : 'a t -> 'b t -> ('a t * 'b t))
     *   (f : Mtcons.t list -> 'a -> 'b -> 'c) t1 t2 =
     * let rec aux cs t1 t2 = match t1,t2 with
     *   | Node { constr = c ; n_true = nt ; n_false = nf ; n_unknwn = nu ; },
     *     Node { constr = c'; n_true = nt'; n_false = nf'; n_unknwn = nu'; }
     *     when c.cpt_uniq = c'.cpt_uniq ->
     *     Node { constr = c;
     *            n_true = aux nt nt';
     *            n_false = aux nf nf';
     *            n_unknwn = aux nu nu'; }
     * 
     *   | Leaf x1, Leaf x2 -> Leaf (f cs x1 x2)
     *   | _ -> raise (Aint_error "Ptree: Shape do not match") in
     * 
     * let t1, t2 = if same_shape t1 t2 then t1,t2 else fmerge t1 t2 in
     * 
     * aux [] t1 t2 *)

  let apply_list (f : 'a list -> 'b) ts =
    let rec aux ts = match ts with
      | [] -> raise (Aint_error "Ptree: apply_l empty list")
      | Node { constr = c; } :: _ ->
        aux_node c ts [] [] []
      | Leaf _ :: _ -> aux_leaf ts []

    and aux_node c ts tts fts uts = match ts with
      | Node { constr = c'; n_true = nt; n_false = nf; n_unknwn = nu; } :: ts'
        when c.cpt_uniq = c'.cpt_uniq ->
        aux_node c ts' (nt :: tts) (nf :: fts) (nu :: uts)
      | [] -> Node { constr   = c;
                     n_true   = aux tts;
                     n_false  = aux fts;
                     n_unknwn = aux uts; }
      | _ -> raise (Aint_error "Ptree: aux_node bad shape")

    and aux_leaf ts xts = match ts with
      | Leaf x :: ts' -> aux_leaf ts' (x :: xts)
      | [] -> Leaf (f xts)
      | _ -> raise (Aint_error "Ptree: aux_leaf bad shape") in

    aux ts

    (* let apply_list (f : Mtcons.t list -> 'a list -> 'b) ts =
     * let rec aux cs ts = match ts with
     *   | [] -> raise (Aint_error "Ptree: apply_l empty list")
     *   | Node (c,_,_) :: _ -> aux_node c cs ts [] []
     *   | Leaf _ :: _ -> aux_leaf cs ts []
     * 
     * and aux_node c cs ts lts rts = match ts with
     *   | Node (c',l,r) :: ts' when c = c' ->
     *     aux_node c cs ts' (l :: lts) (r :: rts)
     *   | [] -> Node (c,
     *                 aux (c.mtcons :: cs) lts,
     *                 aux (flip c.mtcons @ cs ) rts)
     *   | _ -> raise (Aint_error "Ptree: aux_node bad shape")
     * 
     * and aux_leaf cs ts xts = match ts with
     *   | Leaf x :: ts' -> aux_leaf cs ts' (x :: xts)
     *   | [] -> Leaf (f cs xts)
     *   | _ -> raise (Aint_error "Ptree: aux_leaf bad shape") in
     * 
     * aux [] ts *)

  let eval (fn : cnstr -> 'a -> 'a -> 'a -> 'a)
      (fl : 'b -> 'a)
      (t : 'b t) =
    let rec aux = function
      | Node { constr = c; n_true = nt; n_false = nf; n_unknwn = nu; } ->
        fn c (aux nt) (aux nf) (aux nu)
      | Leaf x -> fl x in
    aux t

  let eval2_merge (fmerge : 'b t -> 'c t -> ('b t * 'c t))
      (fn : cnstr -> 'a -> 'a -> 'a -> 'a)
      (fl : 'b -> 'c -> 'a)
      (t1 : 'b t) (t2 : 'c t) =
    let rec aux t1 t2 = match t1,t2 with
      | Node { constr = c ; n_true = nt ; n_false = nf ; n_unknwn = nu ; },
        Node { constr = c'; n_true = nt'; n_false = nf'; n_unknwn = nu'; }
        when c.cpt_uniq = c'.cpt_uniq ->
        fn c (aux nt nt') (aux nf nf') (aux nu nu')
      | Leaf x1, Leaf x2 -> fl x1 x2
      | _ -> raise (Aint_error "Ptree: eval2 : shape do not match") in

    let t1, t2 = if same_shape t1 t2 then t1,t2 else fmerge t1 t2 in

    aux t1 t2


  (*   let eval (fn : cnstr -> 'a -> 'a -> 'a)
   *     (fl : Mtcons.t list -> 'b -> 'a)
   *     (t : 'b t) =
   *   let rec aux cs = function
   *     | Node (c,l,r) ->
   *       fn c (aux (c.mtcons :: cs) l) (aux (flip c.mtcons @ cs) r)
   *     | Leaf x -> fl cs x in
   *   aux [] t
   * 
   * let eval2_merge (fmerge : 'b t -> 'c t -> ('b t * 'c t))
   *     (fn : Mtcons.t list -> 'a -> 'a -> 'a)
   *     (fl : Mtcons.t list -> 'b -> 'c -> 'a)
   *     (t1 : 'b t) (t2 : 'c t) =
   *   let rec aux cs t1 t2 = match t1,t2 with
   *     | Node (c1,l1,r1), Node (c2,l2,r2) when c1 = c2 ->
   *       fn cs (aux (c1.mtcons :: cs) l1 l2) (aux (flip c1.mtcons @ cs) r1 r2)
   *     | Leaf x1, Leaf x2 -> fl cs x1 x2
   *     | _ -> raise (Aint_error "Ptree: eval2 : shape do not match") in
   * 
   *   let t1, t2 = if same_shape t1 t2 then t1,t2 else fmerge t1 t2 in
   * 
   *   aux [] t1 t2 *)

  let ptree_size = eval (fun _ a b c -> a + b + c) (fun _ -> 1)
end


(* Trace partitionning, see the description of the [node] type in 
   the module [Ptree]. *)
module type AbsDisjType = sig
  include AbsNumType

  (* Make a top value with *no* disjunction *)
  val top_no_disj : t -> t

  (* [to_shape t shp] : lifts [t] to the shape of [shp] 
     Remark: [t] must be without disjunction. *)
  val to_shape : t -> t -> t

  val remove_disj : t -> t

  (* of_box uses an already existing disjunctive value to get its shape. *)
  val of_box : Box.t Abstract1.t -> t -> t

  (* Adds a block of constraints for the disjunctive domain *)
  val new_cnstr_blck : t -> L.t -> t

  (* Add a constraint to the top-most block.
     If [meet] is true, meet the resulting branch with, respectively,
     the constraint and its negation. *)
  val add_cnstr : t -> meet:bool -> Mtcons.t -> L.t -> t * t

  (* Pop the top-most block of constraints in the disjunctive domain *)
  val pop_cnstr_blck : t -> L.t -> t

  (* Pop all constraints in the disjunctive domain *)
  val pop_all_blcks : t -> t
end

(*---------------------------------------------------------------*)
type cnstr_blk = { cblk_loc : L.t;
                   cblk_cnstrs : cnstr list; }

(* hashconsing *)
module OrdL = struct 
  type t = L.t
  let compare l l' = Stdlib.compare l.L.loc_start l'.L.loc_start

  let equal l l' =  l.L.loc_start = l'.L.loc_start 
end
module ML = Map.Make (OrdL)
    
let hc = ref ML.empty
let _uniq = ref 0

(* Note that the *)
let make_cnstr c i =
  try
    let constr = ML.find i !hc in
    if Mtcons.equal_tcons constr.mtcons c
    then constr
    else begin
      debug (fun () ->
          Format.eprintf "make_cnstr for (%d, line %a):@.\
                          changed constraint from %a to %a@."
            constr.cpt_uniq L.pp_sloc i
            Mtcons.print_mexpr constr.mtcons
            Mtcons.print_mexpr c);
          { constr with mtcons = c } end
  with
  | Not_found ->
    incr _uniq;
    let res = { mtcons = c; cpt_uniq = !_uniq; loc = i } in
    hc := ML.add i res !hc;
    res

(* Disjunctive domain. Leaves are already constrained under the branch
   conditions. *)
module AbsDisj (A : AbsNumType) : AbsDisjType = struct

  type t = { tree : A.t Ptree.t;
             cnstrs : cnstr_blk list }


  (*---------------------------------------------------------------*)
  let is_spec = ref None 
  let init_is_spec b = match !is_spec with
    | None -> is_spec := Some b; A.init_is_spec b
    | Some _ -> assert false    (* Should not initialize this twice *)

  let init_blk = { cblk_loc = L._dummy; cblk_cnstrs = [] }

  let make_abs a = { tree = Leaf a;
                     cnstrs = [ init_blk ]; }

  (*---------------------------------------------------------------*)
  let pp_cblk fmt cb =
    Format.fprintf fmt "[{%a} %a]"
      L.pp_sloc cb.cblk_loc
      pp_cnstrs cb.cblk_cnstrs 

  let pp_cblks fmt =
    Format.fprintf fmt "@[<v 0>%a@]"
      (pp_list ~sep:(fun fmt () -> Format.fprintf fmt "@;") pp_cblk)
      
  let cblk_equal cb cb' =
    cb.cblk_loc = cb'.cblk_loc
    && List.length cb.cblk_cnstrs = List.length cb'.cblk_cnstrs
    && List.for_all2 (fun c c' -> c.cpt_uniq = c'.cpt_uniq) 
      cb.cblk_cnstrs cb'.cblk_cnstrs

  (*---------------------------------------------------------------*)
  let same_shape t t' =
    List.length t.cnstrs = List.length t'.cnstrs
    && List.for_all2 cblk_equal t.cnstrs t'.cnstrs

  let compare c c' = Stdlib.compare c.cpt_uniq c'.cpt_uniq

  let equal c c' = compare c c' = 0

  let cnstrs_list l = 
    List.map (fun x -> x.cblk_cnstrs) l |> List.rev |> List.flatten

  let add_constr_unknwn c t =
    Ptree.Node { constr   = c;
                 n_true   = Ptree.apply A.bottom t;
                 n_false  = Ptree.apply A.bottom t;
                 n_unknwn = t; }
      
    
  (* Merge two blocks [t] and [t']. If a constraint [c] appears on the left
     but node on the right, replace [t'] by
     [Node { constr = c; n_true = bottom; n_false = bottom; n_unknwn = t'] *)
  let rec merge_blck mcs t t' = match mcs, t, t' with
    | [], Ptree.Leaf _, Ptree.Leaf _ -> t, t'
    | c0 :: mcs',
      Node { constr = c ; n_true = nt ; n_false = nf ; n_unknwn = nu ; },
      Node { constr = c'; n_true = nt'; n_false = nf'; n_unknwn = nu'; } ->
      if equal c c' && equal c c0 then
        let mnt,mnt' = merge_blck mcs' nt nt'
        and mnf,mnf' = merge_blck mcs' nf nf'
        and mnu,mnu' = merge_blck mcs' nu nu' in
        ( Ptree.Node { constr   = c;
                       n_true   = mnt;
                       n_false  = mnf;
                       n_unknwn = mnu; },
          Ptree.Node { constr   = c;
                       n_true   = mnt';
                       n_false  = mnf';
                       n_unknwn = mnu'; } )
      else if equal c c0
      then merge_blck mcs t (add_constr_unknwn c t')
      else if equal c' c0
      then merge_blck mcs (add_constr_unknwn c t) t'
      else raise (Aint_error "merge_blck: bad shape")

    | c0 :: _, Node { constr = c; }, Ptree.Leaf _ ->
      assert (equal c0 c);
      merge_blck mcs t (add_constr_unknwn c t')

    | c0 :: _, Ptree.Leaf _, Node { constr = c'; } ->
      assert (equal c0 c');
      merge_blck mcs (add_constr_unknwn c' t) t'

    | _ -> raise (Aint_error "merge_blck: bad shape")

  let rec merge_last_blck mcs t t' l = match l with
    | [] -> merge_blck mcs t t'
    | c0 :: l' ->
      match t,t' with
      | Ptree.Node {constr = c ; n_true = nt ; n_false = nf ; n_unknwn = nu ;},
        Ptree.Node {constr = c'; n_true = nt'; n_false = nf'; n_unknwn = nu';} 
        when equal c c' && equal c c0 ->
        let mnt,mnt' = merge_last_blck mcs nt nt' l'
        and mnf,mnf' = merge_last_blck mcs nf nf' l'
        and mnu,mnu' = merge_last_blck mcs nu nu' l' in
        ( Ptree.Node {constr   = c ;
                      n_true   = mnt ;
                      n_false  = mnf ;
                      n_unknwn = mnu ;},
          Ptree.Node {constr   = c;
                      n_true   = mnt';
                      n_false  = mnf';
                      n_unknwn = mnu';} )
      | _ -> assert false

  let tmerge_check cs l cs' l' =
    if not (List.for_all2 cblk_equal l l') then begin
      Format.eprintf "error tmerg:@;l:@;%a@.l':@;%a@."
        pp_cblks l
        pp_cblks  l';
      assert false
    end;
    if not (cs.cblk_loc = cs'.cblk_loc) then begin
      Format.eprintf "%a and %a"
        L.pp_sloc cs.cblk_loc L.pp_sloc cs'.cblk_loc;
      assert false
    end

  let tmerge t t' =
    if same_shape t t' then t, t'
    else match t.cnstrs, t'.cnstrs with
      | [], [] -> t,t'
      | cs :: l, cs' :: l' ->
        tmerge_check cs l cs' l';
        let mcs_cnstrs = 
          List.sort_uniq compare (cs.cblk_cnstrs @ cs'.cblk_cnstrs) in
        let mcs = { cs with cblk_cnstrs = mcs_cnstrs } in
        
        let mt, mt' = 
          merge_last_blck mcs_cnstrs t.tree t'.tree (cnstrs_list l) in
        ( { tree = mt; cnstrs = mcs :: l }, { tree = mt'; cnstrs = mcs :: l } )
      | _ -> assert false

  
  let apply f t = { t with tree = Ptree.apply f t.tree }

  let eval fn fl t = Ptree.eval fn fl t.tree

  let bottom a = apply (fun x -> A.bottom x) a
      
  let top a = apply (fun x -> A.top x) a

  let apply2 f t t' =
    let t,t' = tmerge t t' in
    { tree = Ptree.apply2_merge (fun _ _ -> assert false) f t.tree t'.tree;
      cnstrs = t.cnstrs }

  let eval2 fn fl t t' =
    let t,t' = tmerge t t' in
    Ptree.eval2_merge (fun _ _ -> assert false) fn fl t.tree t'.tree

  let merge_list l = match l with
    | [] -> []
    | t :: l' ->
      let t_lce = List.fold_left (fun acc x -> tmerge acc x |> fst) t l' in
      t_lce :: (List.map (fun x -> tmerge t_lce x |> snd) l')

  let apply_list f ts =
    match merge_list ts with
    | [] -> raise (Aint_error "apply_list: empty list")
    | t :: _ as ts ->
      let tts = List.map (fun x -> x.tree) ts in
      { tree = Ptree.apply_list f tts;
        cnstrs = t.cnstrs }

  let new_cnstr_blck t l =
    let blk = { cblk_loc = l; cblk_cnstrs = [] } in
    { t with cnstrs = blk :: t.cnstrs }

  let tbottom a = Ptree.apply (fun x -> A.bottom x) a

  let build_tree_pair c (mnt,mnt') (mnf,mnf') (mnu,mnu') =
    ( Ptree.Node {constr   = c;
                  n_true   = mnt;
                  n_false  = mnf;
                  n_unknwn = mnu;},
      Ptree.Node {constr   = c;
                  n_true   = mnt';
                  n_false  = mnf';
                  n_unknwn = mnu';} )
    
  (* Insert the constraint in the current block at the correct place.
     If [meet] is true, then meet the [n_true] branch with [c] and the 
     [n_false] branch with [not c]. *)
  let add_cnstr_blck ~meet c t =
    let meet_true a =
      if meet
      then A.meet_constr a c.mtcons
      else a 
    and meet_false a =
      if meet
      then match flip_constr c.mtcons with
        | None -> a
        | Some nc -> A.meet_constr a nc
      else a
    in
    
    let rec add_cnstr_blck t = match t with
    | Ptree.Leaf a ->
      let nt = meet_true a
      and nf = meet_false a in

      ( Ptree.Node { constr   = c ;
                     n_true   = Ptree.Leaf nt ;
                     n_false  = Ptree.Leaf (A.bottom a) ;
                     n_unknwn = Ptree.Leaf (A.bottom a) ;},
        Ptree.Node { constr   = c ;
                     n_true   = Ptree.Leaf (A.bottom a) ;
                     n_false  = Ptree.Leaf nf ;
                     n_unknwn = Ptree.Leaf (A.bottom a) ;} )

    | Ptree.Node {constr = c' ; n_true = nt ; n_false = nf ; n_unknwn = nu ;} ->
      let cc = compare c c' in

      (* [c] must be inserted above [c'] *)
      if cc = -1 then
        let nt' = Ptree.apply (fun a -> meet_true a ) t
        and nf' = Ptree.apply (fun a -> meet_false a) t in

      ( Ptree.Node { constr   = c ;
                     n_true   = nt' ;
                     n_false  = tbottom t ;
                     n_unknwn = tbottom t ;},
        Ptree.Node { constr   = c ;
                     n_true   = tbottom t ;
                     n_false  = nf' ;
                     n_unknwn = tbottom t ;} )


      (* [c] must be inserted below [c'] *)
      else if cc = 1 then
        build_tree_pair c'
          (add_cnstr_blck nt) (add_cnstr_blck nf) (add_cnstr_blck nu)

      (* [c] and [c'] are equal. We need to consider cross-cases here.
          c                       c      
          |---- t                 |---- ⟦c⟧ ∪ ⟦c⟧u ∪ ⟦c⟧f
          |---- u       ===>      |---- ⟂
          |---- f                 |---- ⟦¬c⟧ ∪ ⟦¬c⟧u ∪ ⟦¬c⟧f
         which we then split as follows:
         c                                  c                         
         |---- ⟦c⟧ ∪ ⟦c⟧u ∪ ⟦c⟧f            |---- ⟂
         |---- ⟂                      and   |---- ⟂                   
         |---- ⟂                            |---- ⟦¬c⟧ ∪ ⟦¬c⟧u ∪ ⟦¬c⟧f
      *)
      else
        let nt' = Ptree.apply_list (fun l ->
            let l = List.map (fun a -> A.meet_constr a c.mtcons) l in
            A.join_list l
          ) [nt; nf; nu]
        and nf' = Ptree.apply_list (fun l ->
            let l = List.map (fun a -> match flip_constr c.mtcons with
                | None -> a
                | Some nc -> A.meet_constr a nc) l in
            A.join_list l
          ) [nt; nf; nu] in
        ( Ptree.Node { constr   = c;
                       n_true   = nt';
                       n_false  = tbottom nu;
                       n_unknwn = tbottom nu; },
          Ptree.Node { constr   = c;
                       n_true   = tbottom nu;
                       n_false  = nf';
                       n_unknwn = tbottom nu; } )
    in

    add_cnstr_blck t
  
  (* Go down to the last block in t and apply f, then inductively combine the
     results using fn *)
  let rec apply_last_blck fn f t l = match l,t with
    | [], _ -> f t
    | c0 :: l',
      Ptree.Node { constr = c; n_true = nt; n_false = nf; n_unknwn = nu; }
      when equal c c0 ->
      let mnt = apply_last_blck fn f nt l'
      and mnf = apply_last_blck fn f nf l'
      and mnu = apply_last_blck fn f nu l' in
      fn c mnt mnf mnu

    | _ -> raise (Aint_error "apply_last_blck: bad shape err3")

  let add_cnstr t ~meet c loc =
    match t.cnstrs with
    | cs :: l ->     
      let cnstr = make_cnstr c loc in
      let f x = add_cnstr_blck ~meet:meet cnstr x in

      let sorted_cnstrs = 
        List.sort_uniq compare (cnstr :: cs.cblk_cnstrs) in
      let nblk = { cs with cblk_cnstrs = sorted_cnstrs } in
      let ncs = nblk :: l in
      let tl,tr = apply_last_blck build_tree_pair f t.tree (cnstrs_list l) in
      ( { tree = tl; cnstrs = ncs }, { tree = tr; cnstrs = ncs } )

    | _ -> raise (Aint_error "add_cnstr: empty list")

  let pop_cnstr_blck t loc = match t.cnstrs with
    | blk :: l ->
      (* This assert is to check that constraint blocks 'open' and 'close'
         are properly nested. *)
      assert (blk.cblk_loc = loc);
      let f x =
        let tree =
          Ptree.eval
            (fun _ a1 a2 a3 -> A.join_list [a1; a2; a3])
            (fun a -> a) x in
        Ptree.Leaf tree
      and fn c mnt mnf mnu = Ptree.Node {constr   = c;
                                         n_true   = mnt;
                                         n_false  = mnf;
                                         n_unknwn = mnu; } in

      { tree =  apply_last_blck fn f t.tree (cnstrs_list l);
        cnstrs =  l }
    | _ -> raise (Aint_error "pop_cnstr_blck: empty list")

  let pop_all_blcks t = 
    let a = Ptree.eval
        (fun _ a1 a2 a3 -> A.join_list [a1; a2; a3]) (fun a -> a) t.tree in
    make_abs a

  let meet_constr_ne (a : A.t) l =
    let l_f = List.filter (fun c ->
        let cmp = Environment.compare (Mtcons.get_expr c).env (A.get_env a) in
        cmp = -1 || cmp = 0) l in

    match l_f with
    | [] -> a
    | _ :: _ -> A.meet_constr_list a l_f
                      
  (* Make a top value defined on the given variables *)
  let make l = make_abs (A.make l)

  let meet = apply2 A.meet
  let meet_list = apply_list A.meet_list

  let join = apply2 A.join
  let join_list = apply_list A.join_list

  let widening oc = apply2 (A.widening oc)

  let forget_list t l = apply (fun x -> A.forget_list x l) t

  let is_included = eval2 (fun _ a1 a2 a3 -> a1 && a2 && a3) A.is_included
  let is_bottom = eval (fun _ a1 a2 a3 -> a1 && a2 && a3) A.is_bottom

  let rec get_leaf = function
    | Ptree.Node { n_true = nt } -> get_leaf nt
    | Ptree.Leaf x -> x 
      
  (* All leaves should have the same environment *)
  let get_env t = A.get_env (get_leaf t.tree)

  (* All leaves should have the same environment *)
  let top_no_disj a =
    let leaf = A.top (get_leaf a.tree) in
    { cnstrs = [init_blk]; tree = Ptree.Leaf leaf; }

  let to_shape a shp =
    assert (a.cnstrs = [init_blk]);
    let leaf = get_leaf a.tree in
    apply (fun _ -> leaf) shp 

  let remove_disj a =
    (* Note that we could evaluate [a] into a list of abstract elements, and
       do a single join at the end. It may be better. *)
    let a = eval (fun _ b1 b2 b3 -> A.join_list [b1; b2; b3]) (fun x -> x) a in
    {cnstrs = [init_blk]; tree = Ptree.Leaf a; }

  let expand t v l = apply (fun x -> A.expand x v l) t

  let fold t l = apply (fun x -> A.fold x l) t

  let bman : Box.t Manager.t = BoxManager.man
  let box_of_int int = Abstract0.of_box bman 1 0 (Array.init 1 (fun _ -> int))
  let box_join b1 b2 b3 =
    let bs = Array.of_list [b1; b2; b3] in
    Abstract0.join_array bman bs
  let int_of_box b = Abstract0.bound_dimension bman b 0

  (* Interval does not support joins, so we go through level 0 boxes. *)
  let bound_variable t v =
    eval (fun _ -> box_join) (fun x -> A.bound_variable x v |> box_of_int ) t
    |> int_of_box

  let bound_texpr t e =
    eval (fun _ -> box_join) (fun x -> A.bound_texpr x e |> box_of_int ) t
    |> int_of_box

  let assign_expr ?force:(force=false) (t : t) (v : mvar) (e : Mtexpr.t) =
    apply (fun x -> A.assign_expr ~force:force x v e) t

  let meet_constr t c = apply (fun x -> A.meet_constr x c) t
  let meet_constr_list t cs = apply (fun x -> A.meet_constr_list x cs) t

  let unify = apply2 A.unify

  let change_environment t l = apply (fun x -> A.change_environment x l) t

  let remove_vars t l = apply (fun x -> A.remove_vars x l) t

  let to_box = eval
      (fun _ a1 a2 a3 ->
         let ass = Array.of_list [a1; a2; a3] in
         Abstract1.join_array bman ass)
      A.to_box


  let of_box bt tshape = apply (fun _ -> A.of_box bt) tshape

  let shrt_tree t =
    (* See Ptree.eval for the order *)
    let fn c mnt mnf mnu = match mnt, mnf, mnu with
      | Ptree.Leaf lmnt, Ptree.Leaf lmnf, Ptree.Leaf lmnu ->
        if A.is_bottom lmnt && A.is_bottom lmnf && A.is_bottom lmnu
        then Ptree.Leaf lmnt
        else Ptree.Node { constr   = c;
                          n_true   = mnt;
                          n_false  = mnf;
                          n_unknwn = mnu; }
      | _ -> Ptree.Node { constr   = c;
                          n_true   = mnt;
                          n_false  = mnf;
                          n_unknwn = mnu; } in

    let fl a = Ptree.Leaf a in
    
    eval fn fl t

  let print ?full:(full=false) fmt t =
    (* Useful to debug constrait blocks *)
    (* Format.eprintf "debug: constraints:@; %a@.@."
     *   pp_cblks t.cnstrs;     *)
    Ptree.pp_ptree (fun fmt a ->
        if A.is_bottom a then Format.fprintf fmt "⟂@;"
        else A.print ~full:full fmt a) fmt (shrt_tree t)
end


module Lift (A : AbsNumType) : AbsDisjType = struct
  include A

  let top_no_disj a = A.top a

  let to_shape a _ = a

  let remove_disj a = a

  let of_box bt _ = A.of_box bt

  let new_cnstr_blck t _ = t

  let add_cnstr t ~meet c _ =
    ( (if meet then A.meet_constr t c else t),
      if meet then
        match flip_constr c with
        | Some nc -> A.meet_constr t nc
        | None -> t
      else t)

  let pop_cnstr_blck t _ = t

  let pop_all_blcks t = t
end

(**************************************)
(* Building of the partition skeleton *)
(**************************************)

let ty_gvar_of_mvar = function
  | Mvalue (Avar v) -> Some v
  | _ -> None

let swap_op2 op e1 e2 =
  match op with
  | E.Ogt   _ -> e2, e1
  | E.Oge   _ -> e2, e1
  | _         -> e1, e2

let mtexpr_of_bigint env z =
  let mpq_z = Mpq.init_set_str (B.to_string z) ~base:10 in
  Mtexpr.cst env (Coeff.s_of_mpq mpq_z)

module PIMake (PW : ProgWrap) : VDomWrap = struct

  let is_spec = ref None 
  let init_is_spec b = match !is_spec with
    | None -> is_spec := Some b
    | Some _ -> assert false    (* Should not initialize this twice *)


  (* We compute the dependency heuristic graph *)
  let pa_res = Pa.pa_make PW.main PW.prog

  (* We compute the reflexive and transitive clojure of dp *)
  let f (dp : Pa.dp) =
    Mv.map (fun sv ->
        Sv.fold (fun v' s ->
            Sv.union s (Pa.dp_v dp v'))
          sv sv) dp

  let dp = fpt f (Mv.equal Sv.equal) pa_res.pa_dp

  (* Add variables where [sv_ini] flows to. *)
  let add_flow sv_ini =
    Mv.fold (fun v sv v_rel ->
        if Sv.disjoint sv sv_ini then v_rel
        else Sv.add v v_rel
      ) dp sv_ini

  (* Add variables flowing to [sv_ini]. *)
  let add_flow_rev sv_ini =
    Mv.fold (fun v sv v_rel ->
        if Sv.mem v sv_ini then Sv.union sv v_rel
        else v_rel
      ) dp sv_ini

  (* We are relational on a variable v iff:
     - there is a direct flow from the intersection of PW.main.f_args and
     Glob_options.relational to v.
     - the variable is appears in while loops conditions,
     or that modifiy a while loop condition variable. *)
  let sv_ini =
    match PW.param.relationals with
    | None -> PW.main.f_args |> Sv.of_list
    | Some v_rel ->
      List.filter (fun v -> List.mem v.v_name v_rel) PW.main.f_args
      |> Sv.of_list

  let v_rel : Sv.t =
    let v_rel = add_flow sv_ini in
    let v_while = add_flow_rev pa_res.while_vars in
    Sv.union v_rel v_while

  (* v is a pointer variable iff there is a direct flow from the intersection
     of PW.main.f_args and Glob_options.pointers to v. *)
  let pt_ini =
    match PW.param.pointers with
    | None -> PW.main.f_args |> Sv.of_list
    | Some v_pt ->
      List.filter (fun v -> List.mem v.v_name v_pt) PW.main.f_args
      |> Sv.of_list

  let v_pt : Sv.t = add_flow pt_ini

  let pp_rel_vars fmt rel =
    (pp_list (Printer.pp_var ~debug:false)) fmt
      (List.sort (fun v v' -> Stdlib.compare v.v_name v'.v_name)
         (Sv.elements rel))

  let () = debug(fun () ->
      Format.eprintf "@[<hov 2>%d relational variables:@ @,%a@]@;\
                      @[<hov 2>%d pointers:@ @,%a@]@;@."
        (Sv.cardinal v_rel)
        pp_rel_vars v_rel
        (Sv.cardinal v_pt)
        pp_rel_vars v_pt)

  let vdom = function
    | Temp _ | WTemp _ -> assert false

    | MNumInv _ -> Ppl 0        (* Numerical invariant must be relational *)

    | Mvalue (Avar v) | MinValue v ->
      if Sv.mem v v_rel then Ppl 0 else Nrd 0

    | MvarOffset v
    | MmemRange (MemLoc v) ->
      if Sv.mem v v_pt then Ppl 0 else Nrd 0

    | Mglobal _
    | Mvalue (AarrayEl _)
    | Mvalue (Aarray _) -> Nrd 0
end


(***********************************)
(* Numerical Domain With Profiling *)
(***********************************)

module type NumWrap = sig
  val prefix : string
  module Num : AbsNumType
end

module MakeAbsNumProf (A : NumWrap) : AbsNumType with type t = A.Num.t = struct
  include A.Num

  let is_spec = ref None 

  (*----------------------------------------------------------------*)
  (* Profiling for the new functions. 
     We post-pone recording until the module has been initialized. *)
  let to_rec = ref []
  let record s = 
    let f () =
      if oget !is_spec 
      then Prof.record ("Spc."^A.prefix^s) 
      else Prof.record ("Std."^A.prefix^s) in
    to_rec := f :: !to_rec

  let record_doit () =
    List.iter (fun f -> f ()) !to_rec

  let call s = 
    if oget !is_spec 
      then Prof.call ("Spc."^A.prefix^s) 
      else Prof.call ("Std."^A.prefix^s)   


  (*----------------------------------------------------------------*)
  let init_is_spec b = match !is_spec with
    | None -> is_spec := Some b; A.Num.init_is_spec b; record_doit ()
    | Some _ -> assert false    (* Should not initialize this twice *)


  (*----------------------------------------------------------------*)
  let () = record "make"
  let make x =
    let t = Sys.time () in
    let r = A.Num.make x in
    let () = call "make" (Sys.time () -. t) in
    r

  let () = record "is_bottom"
  let is_bottom x =
    let t = Sys.time () in
    let r = A.Num.is_bottom x in
    let () = call "is_bottom" (Sys.time () -. t) in
    r

  let () = record "bottom"
  let bottom x =
    let t = Sys.time () in
    let r = A.Num.bottom x in
    let () = call "bottom" (Sys.time () -. t) in
    r

  let () = record "meet_list"
  let meet_list x =
    let t = Sys.time () in 
    let r = A.Num.meet_list x in
    let () = call "meet_list" (Sys.time () -. t) in
    r

  let () = record "join_list"
  let join_list x =
    let t = Sys.time () in
    let r = A.Num.join_list x in
    let () = call "join_list" (Sys.time () -. t) in
    r

  let () = record "meet"
  let meet x y =
    let t = Sys.time () in
    let r = A.Num.meet x y in
    let () = call "meet" (Sys.time () -. t) in
    r

  let () = record "join"
  let join x y =
    let t = Sys.time () in
    let r = A.Num.join x y in
    let () = call "join" (Sys.time () -. t) in
    r

  let () = record "widening"
  let widening x y =
    let t = Sys.time () in
    let r = A.Num.widening x y in
    let () = call "widening" (Sys.time () -. t) in
    r

  let () = record "is_included"
  let is_included x y =
    let t = Sys.time () in
    let r = A.Num.is_included x y in
    let () = call "is_included" (Sys.time () -. t) in
    r

  let () = record "forget_list"
  let forget_list x y =
    let t = Sys.time () in
    let r = A.Num.forget_list x y in
    let () = call "forget_list" (Sys.time () -. t) in
    r

  let () = record "fold"
  let fold x y =
    let t = Sys.time () in
    let r = A.Num.fold x y in
    let () = call "fold" (Sys.time () -. t) in
    r

  let () = record "bound_variable"
  let bound_variable x y =
    let t = Sys.time () in
    let r = A.Num.bound_variable x y in
    let () = call "bound_variable" (Sys.time () -. t) in
    r

  let () = record "bound_texpr"
  let bound_texpr x y =
    let t = Sys.time () in
    let r = A.Num.bound_texpr x y in
    let () = call "bound_texpr" (Sys.time () -. t) in
    r

  let () = record "meet_constr"
  let meet_constr x y =
    let t = Sys.time () in
    let r = A.Num.meet_constr x y in
    let () = call "meet_constr" (Sys.time () -. t) in
    r

  let () = record "unify"
  let unify x y =
    let t = Sys.time () in
    let r = A.Num.unify x y in
    let () = call "unify" (Sys.time () -. t) in
    r

  let () = record "expand"
  let expand x y z =
    let t = Sys.time () in
    let r = A.Num.expand x y z in
    let () = call "expand" (Sys.time () -. t) in
    r

  let () = record "assign_expr"
  let assign_expr ?force:(force=false) x y z =
    let t = Sys.time () in
    let r = A.Num.assign_expr ~force:force x y z in
    let () = call "assign_expr" (Sys.time () -. t) in
    r

  let () = record "to_box"
  let to_box x =
    let t = Sys.time () in
    let r = A.Num.to_box x in
    let () = call "to_box" (Sys.time () -. t) in
    r

  let () = record "of_box"
  let of_box x =
    let t = Sys.time () in
    let r = A.Num.of_box x in
    let () = call "of_box" (Sys.time () -. t) in
    r

end

module type DisjWrap = sig
  val prefix : string
  module Num : AbsDisjType
end

module MakeAbsDisjProf (A : DisjWrap) : AbsDisjType = struct
  module AProf = MakeAbsNumProf (struct
      let prefix = A.prefix
      module Num = struct
        include A.Num
        let of_box _ = assert false
      end
    end)

  include AProf

  let of_box         = A.Num.of_box
  let new_cnstr_blck = A.Num.new_cnstr_blck
  let add_cnstr      = A.Num.add_cnstr
  let pop_cnstr_blck = A.Num.pop_cnstr_blck
  let pop_all_blcks  = A.Num.pop_all_blcks
  let to_shape       = A.Num.to_shape
  let top_no_disj    = A.Num.top_no_disj
  let remove_disj    = A.Num.remove_disj

  let is_spec = ref None 

  (*----------------------------------------------------------------*)
  (* Profiling for the new functions. 
     We post-pone recording until the module has been initialized. *)
  let to_rec = ref []
  let record s = 
    let f () =
      if oget !is_spec 
      then Prof.record ("Spc.D."^s) 
      else Prof.record ("Std.D."^s) in
    to_rec := f :: !to_rec

  let record_doit () =
    List.iter (fun f -> f ()) !to_rec

  let call s = 
    if oget !is_spec 
      then Prof.call ("Spc.D."^s) 
      else Prof.call ("Std.D."^s) 

  (*----------------------------------------------------------------*)
  let init_is_spec b = match !is_spec with
    | None -> is_spec := Some b; AProf.init_is_spec b; record_doit ();
    | Some _ -> assert false    (* Should not initialize this twice *)

  (*----------------------------------------------------------------*)
  let () = record "of_box"
  let of_box x y =
    let t = Sys.time () in
    let r = of_box x y in
    let () = call "of_box" (Sys.time () -. t) in
    r

  let () = record "to_shape"
  let to_shape x y =
    let t = Sys.time () in
    let r = to_shape x y in
    let () = call "to_shape" (Sys.time () -. t) in
    r

  let () = record "top_no_disj"
  let top_no_disj x =
    let t = Sys.time () in
    let r = top_no_disj x in
    let () = call "top_no_disj" (Sys.time () -. t) in
    r

  let () = record "remove_disj"
  let remove_disj x =
    let t = Sys.time () in
    let r = remove_disj x in
    let () = call "remove_disj" (Sys.time () -. t) in
    r

  let () = record "new_cnstr_blck"
  let new_cnstr_blck x =
    let t = Sys.time () in
    let r = new_cnstr_blck x in
    let () = call "new_cnstr_blck" (Sys.time () -. t) in
    r

  let () = record "add_cnstr"
  let add_cnstr x ~meet y z =
    let t = Sys.time () in
    let r = add_cnstr x ~meet y z in
    let () = call "add_cnstr" (Sys.time () -. t) in
    r

  let () = record "pop_cnstr_blck"
  let pop_cnstr_blck x loc =
    let t = Sys.time () in
    let r = pop_cnstr_blck x loc in
    let () = call "pop_cnstr_blck" (Sys.time () -. t) in
    r

  let () = record "pop_all_blcks"
  let pop_all_blcks x =
    let t = Sys.time () in
    let r = pop_all_blcks x in
    let () = call "pop_all_blcks" (Sys.time () -. t) in
    r

end


(*************************************************)
(* Numerical Domain with Two Levels of Precision *)
(*************************************************)

module type AbsNumT = sig
  module R : AbsDisjType
  module NR : AbsNumType

  (* C.f. AbsBoolNoRel desciption *)
  val init_is_spec : bool -> unit

  val downgrade : R.t -> NR.t
  (* The second argument is used as a shape *)
  val upgrade : NR.t -> R.t -> R.t
end


module AbsNumTMake (PW : ProgWrap) : AbsNumT = struct
  module VDW = PIMake (PW)

  module RProd =
    AbsNumProd (VDW) (AbsNumI (BoxManager) (PW)) (AbsNumI (PplManager) (PW))

  module RNum = AbsDisj (RProd)

  module R = MakeAbsDisjProf (struct
      module Num = RNum
      let prefix = "R."
    end)

  module NRNum = AbsNumI (BoxManager) (PW)

  module NR = MakeAbsNumProf (struct
      module Num = NRNum
      let prefix = "NR."
    end)

  let is_spec = ref None 
  let init_is_spec b = match !is_spec with
    | None -> 
      is_spec := Some b; 
      VDW.init_is_spec b; 
      R.init_is_spec b;
      NR.init_is_spec b
    | Some _ -> assert false    (* Should not initialize this twice *)

  let downgrade a = NR.of_box (R.to_box a)

  let upgrade a tshape = R.of_box (NR.to_box a) tshape
end


(*****************************)
(* Points-to Abstract Domain *)
(*****************************)

(* Pointer expressions *)
type ptr_expr = PtVars of mvar list | PtTopExpr

(* Symbolic pointers *)
type ptrs = Ptrs of mem_loc list | TopPtr

let pp_memloc fmt = function MemLoc v -> Format.fprintf fmt "%s" v.v_name

let pp_memlocs fmt l =
  pp_list ~sep:(fun fmt () -> Format.fprintf fmt "@ ") pp_memloc fmt l

let pp_ptr fmt = function
  | Ptrs m -> Format.fprintf fmt "%a" pp_memlocs m
  | TopPtr -> Format.fprintf fmt "#TopPtr"


module type PointsTo = sig
  type t

  (* make takes as input the set of memory locations of the program *)
  val make : mem_loc list -> t

  val meet : t -> t -> t
  val join : t -> t -> t

  val widening : t -> t -> t

  val forget_list : t -> mvar list -> t
  val is_included : t -> t -> bool

  (* val top_mem_loc : t -> mem_loc list *)

  val expand : t -> mvar -> mvar list -> t
  val fold : t -> mvar list -> t

  val var_points_to : t -> mvar -> ptrs
  val assign_ptr_expr : t -> mvar -> ptr_expr -> t

  val unify : t -> t -> t

  val print : Format.formatter -> t -> unit
end

module PointsToImpl : PointsTo = struct
  (* Points-to abstract value *)
  type t = { pts : mem_loc list Ms.t }
             (* top : mem_loc list } *)

  let make mls =
    let string_of_var v = match v.v_ty with
      | Arr _ -> raise (Aint_error "Array(s) in export function's inputs")
      | Bty _ -> string_of_mvar (Mvalue (Avar v)) in

    let pts = List.fold_left (fun pts x -> match x with
        | MemLoc v -> Ms.add (string_of_var v) [x] pts)
        Ms.empty mls in
    { pts = pts }
    (* { pts = pts ; top = mls } *)

  let meet : t -> t -> t = fun t t' ->
    let pts'' =
      Ms.merge (fun _ aop bop -> match aop,bop with
          | None, x | x, None -> x (* None corresponds to TopPtr *)

          | Some l, Some l' ->
            let l_inter = List.filter (fun x -> List.mem x l') l in
            Some (List.sort_uniq Stdlib.compare l_inter )
        ) t.pts t'.pts in

    { t with pts = pts'' }

  let join : t -> t -> t = fun t t' ->
    let pts'' =
      Ms.merge (fun _ aop bop -> match aop,bop with
          | None, _ | _, None -> None (* None corresponds to TopPtr *)

          | Some l, Some l' ->
            Some (List.sort_uniq Stdlib.compare (l @ l'))
        ) t.pts t'.pts in

    { t with pts = pts'' }

  let widening t t' = join t t'

  let svar_points_to : t -> string -> ptrs = fun t s_var ->
    if Ms.mem s_var t.pts then Ptrs (Ms.find s_var t.pts)
    else TopPtr

  let var_points_to : t -> mvar -> ptrs = fun t var ->
    (* We correctly tracked points-to information only for 
       variables (e.g. array elements are not properly handled, and
       consequently can point to anybody.). *)
    match var with
    | Mvalue (Avar _) -> svar_points_to t (string_of_mvar var)
    | _ -> TopPtr

  let forget_list : t -> mvar list -> t = fun t l_rem ->
    let l_rem = u8_blast_vars ~blast_arrays:true l_rem in
    let vl_rem = List.map string_of_mvar l_rem in
    { t with pts = Ms.filter (fun v _ -> not (List.mem v vl_rem)) t.pts }

  let is_included : t -> t -> bool = fun t t' ->
    Ms.for_all (fun v l ->
        if not (Ms.mem v t'.pts) then true
        else
          let l' = Ms.find v t'.pts in
          List.for_all (fun x -> List.mem x l') l
      ) t.pts

  (* let top_mem_loc : t -> mem_loc list = fun t -> t.top *)

  let join_ptrs_list ptrss =
    let rec aux acc = function
      | [] -> Ptrs (List.sort_uniq Stdlib.compare acc)
      | TopPtr :: _ -> TopPtr
      | Ptrs l :: tail -> aux (l @ acc) tail in

    aux [] ptrss

  let pt_assign : t -> string -> ptrs -> t = fun t v ptrs -> match ptrs with
    | Ptrs vpts -> { t with pts = Ms.add v vpts t.pts }
    | TopPtr -> { t with pts = Ms.remove v t.pts }

  let assign_ptr_expr : t -> mvar -> ptr_expr -> t = fun t v e -> match e with
    | PtTopExpr -> { t with pts = Ms.remove (string_of_mvar v) t.pts }
    | PtVars el ->
      let v_pts =
        List.fold_left (fun acc var ->
            var_points_to t var :: acc) [] el
        |> join_ptrs_list in

      pt_assign t (string_of_mvar v) v_pts

  let unify : t -> t -> t = meet

  let expand : t -> mvar -> mvar list -> t = fun t v l ->
    let v_pts = var_points_to t v in
    List.fold_left (fun t v' -> pt_assign t (string_of_mvar v') v_pts ) t l

  let fold : t -> mvar list -> t = fun t l -> match l with
    | [] -> assert false
    | v :: tail ->
      let t' = assign_ptr_expr t v (PtVars l) in
      forget_list t' tail

  let print ppf t =
    Format.fprintf ppf "@[<hov 4>* Points-to:@ %a@]@;"
      (pp_list ~sep:(fun _ _ -> ()) (fun ppf (k,l) ->
           if l <> [] then
             Format.fprintf ppf "%s: %a;@,"
               k pp_memlocs l;))
      (List.filter (fun (x,_) -> not (svariables_ignore x)) (Ms.bindings t.pts))

end



(*****************************************)
(* Maps with Equivalence Classes of Keys *)
(*****************************************)

module type Ordered = sig
  type t
  val compare : t -> t -> int
end

module Mc = Map.Int

module Map2 (M : Map.S) = struct
  let map2 : ('a -> 'b -> 'c) -> 'a M.t -> 'b M.t -> 'c M.t =
    fun f map_a map_b ->
      M.mapi (fun k a ->
          let b = M.find k map_b in
          f a b)
        map_a

  let merge2 : (unit -> 'a) -> (unit -> 'b) -> 'a M.t -> 'b M.t -> ('a M.t * 'b M.t)=
    fun fa fb mapa mapb ->
      (M.merge (fun _ aopt _ -> match aopt with
           | None -> fa () |> some
           | Some a -> Some a)
          mapa mapb,
       M.merge (fun _ _ bopt -> match bopt with
           | None -> fb () |> some
           | Some b -> Some b)
         mapa mapb)
end

module type EqMap = sig
  type key
  type 'a t

  val empty : 'a t

  (* Number of equivalence classes. *)
  val csize : 'a t -> int

  (* Fold over equivalence classes *)
  val cfold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val mem: key -> 'a t -> bool

  val find: key -> 'a t -> 'a

  val adds: key list -> 'a -> 'a t -> 'a t

  val removes: key list -> 'a t -> 'a t

  val iter: (key -> 'a -> unit) -> 'a t -> unit
      
  val map: ('a -> 'b) -> 'a t -> 'b t

  val map2 : ('a -> 'a -> 'c) -> 'a t -> 'a t -> 'c t

  val kfilter : (key -> bool) -> 'a t -> 'a t

  val vmerge:
    ('a option -> 'a option -> 'b option) -> 'a t -> 'a t -> 'b t
end

module MakeEqMap (K : Ordered) : EqMap with type key = K.t = struct
  type key = K.t

  module Mk = Map.Make(K)

  type 'a t = { ktoc : int Mk.t;
                ctov : 'a Mc.t;
                _cpt : int }

  let empty = { ktoc = Mk.empty;
                ctov = Mc.empty;
                _cpt = 0 }

  let csize t = Mc.cardinal t.ctov

  let newc t = ({ t with _cpt = t._cpt + 1 }, t._cpt)

  let mem k t = try Mc.mem (Mk.find k t.ktoc) t.ctov with Not_found -> false

  let find k t = Mc.find (Mk.find k t.ktoc) t.ctov

  let adds ks a t =
    let t,i = newc t in
    let ktoc =
      List.fold_left (fun ktoc k -> Mk.add k i ktoc) t.ktoc ks in
    { t with ktoc = ktoc; ctov = Mc.add i a t.ctov }

  let iter f t = Mk.iter (fun k c -> f k (Mc.find c t.ctov)) t.ktoc
                
  let map f t = { t with ctov = Mc.map f t.ctov }

  (* Fold over classes. *)
  let cfold f t a = Mc.fold (fun _ x y -> f x y) t.ctov a

  (* This function unifies the equivalence classes of t and t' *)
  let unify_classes : 'a t -> 'b t -> int * int Mk.t * 'a Mc.t * 'b Mc.t =
    fun t t' ->
      let open Utils in
      let module Sk = Set.Make(K) in
      (* This function groupe keys in the same equivalence class *)
      let rec grp l = match l with
        | [] | _ :: [] -> l
        | (x1,l1) :: (x2,l2) :: l' ->
          if x1 = x2 then grp ((x1,Sk.union l1 l2) :: l')
          else (x1,l1) :: grp ((x2,l2) :: l') in

      let s_binds x =
        Mk.bindings x.ktoc
        |> List.stable_sort (fun (_,i) (_,i') -> Stdlib.compare i i')
        |> List.map (fun (x,y) -> (y,Sk.singleton x))
        |> grp in

      let lt,lt' = s_binds t,s_binds t' in
      let ltk = List.fold_left (fun sk (_,sk') ->
          Sk.union sk sk') Sk.empty lt in
      let ltk' = List.fold_left (fun sk (_,sk') ->
          Sk.union sk sk') Sk.empty lt' in

      (* Tedious *)
      let rec merge_ne f_next lt lt' cpt mk mc mc' t t' ltk ltk' = match lt with
        (* We inverse the arguments ! *)
        | [] -> f_next lt' lt cpt mk mc' mc t' t ltk' ltk

        | (i,l) :: r ->
          let k = Sk.any l in
          let oi' = try Some (Mk.find k t'.ktoc) with Not_found -> None in
          let l' = match obind (fun i' -> List.assoc_opt i' lt') oi' with
            | Some s -> s
            | None -> Sk.empty in
          let join =
            Sk.union
              (Sk.inter l l')
              (Sk.union
                 (Sk.diff l ltk')
                 (Sk.diff l' ltk)) in
          let mk = Sk.fold (fun k mk -> Mk.add k cpt mk) join mk in
          let mc = Mc.add cpt (Mc.find i t.ctov) mc in
          let mc' = match oi' with
            | None -> mc'
            | Some i' -> Mc.add cpt (Mc.find i' t'.ctov) mc' in

          let nl, nl' = Sk.diff l join, Sk.diff l' join in
          let nlt = if Sk.is_empty nl then r else (i,nl) :: r in
          let nlt' = match oi' with
            | None -> lt'
            | Some i' ->
              if Sk.is_empty nl' then List.remove_assoc i' lt'
              else assoc_up i' (fun _ -> nl') lt' in

          merge_ne f_next nlt nlt' (cpt + 1) mk mc mc' t t' ltk ltk' in

      merge_ne (merge_ne (fun _ _ cpt mk mc mc' _ _ _ _ -> (cpt,mk,mc,mc')))
        lt lt' 0 Mk.empty Mc.empty Mc.empty t t' ltk ltk'

  let map2 f t t' =
    let cpt,mk,mc,mc' = unify_classes t t' in
    let module M2 = Map2(Mc) in
    { ktoc = mk;
      ctov = M2.map2 f mc mc';
      _cpt = cpt }

  let kfilter (f : key -> bool) (t : 'a t) =
    let module Si = Set.Int in
    let ktoc = Mk.filter (fun k _ -> f k) t.ktoc in
    let si = Mk.fold (fun _ i sk -> Si.add i sk) ktoc Si.empty in
    let ctov = Mc.filter (fun i _ -> Si.mem i si) t.ctov in
    { t with ctov = ctov; ktoc = ktoc }

  let removes (ks : key list) (t : 'a t) =
    kfilter (fun k -> not (List.mem k ks)) t

  let vmerge f t t' =
    let cpt,mk,mc,mc' = unify_classes t t' in
    let mr = Mk.fold (fun _ i mr ->
        if Mc.mem i mr then mr
        else
          let ov = Mc.Exceptionless.find i mc
          and ov' = Mc.Exceptionless.find i mc' in
          match f ov ov' with
          | None -> mr
          | Some rv -> Mc.add i rv mr)
        mk Mc.empty in
    let mk = Mk.filter (fun _ i -> Mc.mem i mr) mk in
    { ktoc = mk; ctov = mr; _cpt = cpt }
end

module EMs = MakeEqMap(Scmp)


(************************************************)
(* Abstraction of numerical and boolean values. *)
(************************************************)

(* Extends a numerical domain to include boolean variable abstractions and
   keep track of initialized variables and points-to information *)
module type AbsNumBoolType = sig
  type t

  (* Must be called exactly once, to set whether the domain is for a 
     speculative or standard semantics.
     Under a speculative semantics, all non-register variables must be handle as
     weak variables (i.e. weak-memory update). *)
  val init_is_spec : bool -> unit

  (* Make a top value defined on the given variables *)
  val make : mvar list -> mem_loc list -> t

  val meet : t -> t -> t
  val join : t -> t -> t
  val widening : Mtcons.t option -> t -> t -> t

  val forget_list : t -> mvar list -> t
  val forget_bvar : t -> mvar -> t

  val is_included : t -> t -> bool
  val is_bottom : t -> bool

  val expand : t -> mvar -> mvar list -> t
  val fold : t -> mvar list -> t

  val bound_variable : t -> mvar -> Interval.t
  val bound_texpr : t -> Mtexpr.t -> Interval.t

  (* Does not change the points-to information *)
  val assign_sexpr : ?force:bool -> t -> mvar -> s_expr -> t
  val assign_bexpr : t -> mvar -> btcons -> t

  val var_points_to : t -> mvar -> ptrs
  val assign_ptr_expr : t -> mvar -> ptr_expr -> t

  val meet_btcons : t -> btcons -> t

  (* Unify the two abstract values on their least common environment. *)
  val unify : t -> t -> t

  (* Variables that are removed are first existentially quantified, and
     variables that are introduced are unconstrained. *)
  val change_environment : t -> mvar list -> t
  val remove_vars : t -> mvar list -> t

  (* Make a top value define on the same variables that the argument.
     All variables are assumed *not* initialized.
     All variables alias to everybody. 
     There are no disjunction. *)
  val top_ni : t -> t

  (* [to_shape t shp] : lifts [t] to the shape of [shp] 
     Remark: [t] must be without disjunction. *)
  val to_shape : t -> t -> t

  val remove_disj : t -> t

  val is_init    : t -> atype -> t
  val copy_init  : t -> mvar -> mvar -> t
  val check_init : t -> atype -> bool

  (* Apron environment. This does not include the boolean variables, nor the
     initialization variables. *)
  val get_env : t -> Environment.t

  val print : ?full:bool -> Format.formatter -> t -> unit

  val new_cnstr_blck : t -> L.t -> t
  val add_cnstr      : t -> meet:bool -> Mtcons.t -> L.t -> t * t
  val pop_cnstr_blck : t -> L.t -> t
  val pop_all_blcks  : t -> t
end


(* Add boolean variable abstractions and keep track of initialized variables 
   and points-to information.
   The boolean abstraction use a non-relational abstract domain. *)
module AbsBoolNoRel (AbsNum : AbsNumT) (Pt : PointsTo)
  : AbsNumBoolType = struct

  (* <Ms.find s init> is an over-approximation of the program state where s
     is *not* initialized.
     Remark: we lazily populate init and bool*)
  type t = { bool : AbsNum.NR.t Mbv.t;
             init : AbsNum.NR.t EMs.t; 
             num : AbsNum.R.t;
             points_to : Pt.t }

  let is_spec = ref None 
  let init_is_spec b = match !is_spec with
    | None -> is_spec := Some b; AbsNum.init_is_spec b
    | Some _ -> assert false    (* Should not initialize this twice *)

  module Mbv2 = Map2(Mbv)

  let merge_bool_dom t t' =
    let eb,eb' = Mbv2.merge2
        (fun () -> AbsNum.downgrade t.num)
        (fun () -> AbsNum.downgrade t'.num)
        t.bool t'.bool in
    ({ t with bool = eb }, { t' with bool = eb' })

  let merge_init_dom t t' =
    let eb = EMs.vmerge (fun x _ -> match x with
        | None -> Some (AbsNum.downgrade t.num)
        | Some _ -> x) t.init t'.init
    and eb' = EMs.vmerge (fun x _ -> match x with
        | None -> Some (AbsNum.downgrade t'.num)
        | Some _ -> x) t'.init t.init in
    ({ t with init = eb }, { t' with init = eb' })

  let apply f df fpt t = { bool = Mbv.map df t.bool;
                           init = EMs.map df t.init;
                           num = f t.num;
                           points_to = fpt t.points_to }

  (* Since init and bool are lazily populated, we merge the domains before 
     applying f *)
  let apply2 f df fpt t t' =
    let t, t' = merge_init_dom t t' in
    let t, t' = merge_bool_dom t t' in
    { bool = Mbv2.map2 df t.bool t'.bool;
      init = EMs.map2 df t.init t'.init;
      num = f t.num t'.num;
      points_to = fpt t.points_to t'.points_to }

  (* [for_all2 f a b b_dfl]
     Iters over the first map *)
  let for_all2 : ('a -> 'b option -> 'c) -> 'a Mbv.t -> 'b Mbv.t -> bool =
    fun f map_a map_b ->
      Mbv.for_all (fun k a ->
          let b = Mbv.find_opt k map_b in
          f a b)
        map_a

  let rec bool_vars = function
    | [] -> []
    | h :: t ->
      if ty_mvar h = Bty Bool then
        (Bvar.make h true) :: (Bvar.make h false) :: bool_vars t
      else bool_vars t

  let rec init_vars = function
    | [] -> []
    | Mvalue at :: t -> string_of_mvar (Mvalue at) :: init_vars t
    | _ :: t -> init_vars t

  let make : mvar list -> mem_loc list -> t = fun l mls ->
    let b_vars = bool_vars l in
    let abs = AbsNum.R.make l in
    let dabs = AbsNum.downgrade abs in

    let bmap = List.fold_left (fun bmap bv ->
        Mbv.add bv dabs bmap) Mbv.empty b_vars in
    { bool = bmap;
      init = EMs.empty;
      num = abs;
      points_to = Pt.make mls }

  let unify_map : AbsNum.NR.t Mbv.t -> AbsNum.NR.t Mbv.t -> AbsNum.NR.t Mbv.t =
    fun b b' ->
      let eb = Mbv.merge (fun _ x y -> match x with
          | None -> y
          | Some _ -> x) b b'
      and eb' = Mbv.merge (fun _ x y -> match x with
          | None -> y
          | Some _ -> x) b' b in
      Mbv2.map2 AbsNum.NR.unify eb eb'


  let eunify_map : AbsNum.NR.t EMs.t -> AbsNum.NR.t EMs.t -> AbsNum.NR.t EMs.t =
    fun b b' ->
      let eb = EMs.vmerge (fun x y -> match x with
          | None -> y
          | Some _ -> x) b b'
      and eb' = EMs.vmerge (fun x y -> match x with
          | None -> y
          | Some _ -> x) b' b in
      EMs.map2 AbsNum.NR.unify eb eb'

  let meet : t -> t -> t = fun t t' ->
    let t,t' = merge_bool_dom t t' in
    { bool = Mbv2.map2 AbsNum.NR.meet t.bool t'.bool;
      init = eunify_map t.init t'.init;
      num = AbsNum.R.meet t.num t'.num;
      points_to = Pt.meet t.points_to t'.points_to }

  let join t t' =
    if AbsNum.R.is_bottom t.num       then t'
    else if AbsNum.R.is_bottom t'.num then t
    else apply2 AbsNum.R.join AbsNum.NR.join Pt.join t t'

  let widening : Mtcons.t option -> t -> t -> t = fun oc ->
    apply2 (AbsNum.R.widening oc) (AbsNum.NR.widening oc) Pt.widening

  let forget_list : t -> mvar list -> t = fun t l ->
    let f x = AbsNum.R.forget_list x l
    and df x = AbsNum.NR.forget_list x l
    and f_pts x = Pt.forget_list x l in
    apply f df f_pts t

  let forget_bvar : t -> mvar -> t  = fun t bv ->
    let dnum = AbsNum.downgrade t.num in
    let t_bv, f_bv = Bvar.make bv true, Bvar.make bv false in
    let bool = Mbv.add t_bv dnum t.bool
               |> Mbv.add f_bv dnum in
    { t with bool = bool }

  (* No need to check anything on t.init and t'.init. *)
  let is_included : t -> t -> bool = fun t t' ->
    let check_b b b_opt' = 
      let b' = match b_opt' with
        | None -> AbsNum.downgrade t'.num
        | Some b' -> b' in
      AbsNum.NR.is_included b b' in

    (AbsNum.R.is_included t.num t'.num)
    && (for_all2 check_b t.bool t'.bool)
    && (Pt.is_included t.points_to t'.points_to)

  (* let top_mem_loc : t -> mem_loc list = fun t -> Pt.top_mem_loc t.points_to *)

  let is_bottom : t -> bool = fun t -> AbsNum.R.is_bottom t.num

  let bound_variable : t -> mvar -> Interval.t = fun t v ->
    AbsNum.R.bound_variable t.num v

  let bound_texpr : t -> Mtexpr.t -> Interval.t = fun t e ->
    AbsNum.R.bound_texpr t.num e

  let expand : t -> mvar -> mvar list -> t = fun t v vl ->
    let f x = AbsNum.R.expand x v vl
    and df x = AbsNum.NR.expand x v vl
    and f_pts x = Pt.expand x v vl in
    apply f df f_pts t

  let fold : t -> mvar list -> t = fun t vl ->
    let f x = AbsNum.R.fold x vl
    and df x = AbsNum.NR.fold x vl in
    let f_pts x = Pt.fold x vl in
    apply f df f_pts t

  (* abs_beval t bexpr : evaluate bexpr in t.
     We split disequalities in two cases to improve precision. *)
  let rec abs_eval_btcons : t -> btcons -> AbsNum.R.t = fun t bexpr ->
    match bexpr with
    | BLeaf c -> begin match Mtcons.get_typ c with
        | Tcons0.DISEQ ->
          let bexpr_pos = BLeaf (Mtcons.make (Mtcons.get_expr c) Tcons0.SUP) in

          let minus_expr = Mtexpr.unop Texpr0.Neg (Mtcons.get_expr c) in
          let bexpr_neg = BLeaf (Mtcons.make minus_expr Tcons0.SUP) in

          abs_eval_btcons t (BOr (bexpr_pos,bexpr_neg))
        | _ -> AbsNum.R.meet_constr t.num c end

    | BVar bv ->
      begin try
          let ab = Mbv.find bv t.bool in
          AbsNum.upgrade ab t.num with
      | Not_found -> t.num end

    | BOr (l_bexpr, r_bexpr) ->
      AbsNum.R.join
        (abs_eval_btcons t l_bexpr)
        (abs_eval_btcons t r_bexpr)

    | BAnd (l_bexpr, r_bexpr) ->
      AbsNum.R.meet
        (abs_eval_btcons t l_bexpr)
        (abs_eval_btcons t r_bexpr)

  let abs_eval_neg_btcons t bexpr = match flip_btcons bexpr with
    | None -> t.num
    | Some c -> abs_eval_btcons t c

  (* Assign an expression given by a list of constrained expressions.
     We do not touch init and points_to there, this has to be done by manualy
     by the caller.
     We unpopulate init to be faster. This is sound if the evaluation of an
     expression neither modifies init not depend on it. *)
  let assign_sexpr : ?force:bool -> t -> mvar -> s_expr -> t =
    fun ?force:(force=false) t v s_expr ->
      let s_init = t.init in
      let points_to_init = t.points_to in
      let t = { t with init = EMs.empty } in

      let n_env = AbsNum.R.get_env t.num in
      let constr_expr_list =
        List.map (fun (bexpr_list, expr) ->
            match bexpr_list with
            | [] -> (None,expr)
            | _ ->
              let constr = List.map (abs_eval_btcons t) bexpr_list
                           |> AbsNum.R.meet_list  in
              (Some constr,expr))
          s_expr in

      let t_list =
        List.map (fun (constr,expr) -> match expr with
            | Some e ->
              let e = Mtexpr.extend_environment e n_env in
              let t' = match constr with
                | None -> t
                | Some c ->
                  let dc = AbsNum.downgrade c in
                  apply (AbsNum.R.meet c) (AbsNum.NR.meet dc) (fun x -> x) t in
              apply
                (fun x -> AbsNum.R.assign_expr ~force:force x v e)
                (fun x -> AbsNum.NR.assign_expr ~force:force x v e)
                (fun x -> x) t'

            | None ->
              let t' = match constr with
                | None -> t
                | Some c ->
                  let dc = AbsNum.downgrade c in
                  apply (AbsNum.R.meet c) (AbsNum.NR.meet dc) (fun x -> x) t in
              apply
                (fun x -> AbsNum.R.forget_list x [v])
                (fun x -> AbsNum.NR.forget_list x [v])
                (fun x -> x) t'              
          ) 
          constr_expr_list in

      (* We compute the join of all the assignments *)
      let join_map b_list = match b_list with
        | [] -> assert false
        | h :: l ->
          Mbv.mapi (fun key x ->
              let elems = x :: List.map (Mbv.find key) l in
              AbsNum.NR.join_list elems) h in

      let b_list,n_list = List.map (fun x -> x.bool) t_list,
                          List.map (fun x -> x.num) t_list in

      { bool = join_map b_list;
        init = s_init;
        num = AbsNum.R.join_list n_list;
        points_to = points_to_init }

  (* Assign a boolean expression.
     As we did in assign_sexpr, we unpopulate init *)
  let assign_bexpr t vb bexpr =
    let s_init = t.init in
    let points_to_init = t.points_to in

    let t = { t with init = EMs.empty } in

    let t_vb, f_vb = Bvar.make vb true,
                     Bvar.make vb false in

    let new_b =
      Mbv.add t_vb (abs_eval_btcons t bexpr |> AbsNum.downgrade) t.bool
      |> Mbv.add f_vb (abs_eval_neg_btcons t bexpr |> AbsNum.downgrade) in

    { bool = new_b;
      init = s_init;
      num = t.num;
      points_to = points_to_init }

  let var_points_to t v = Pt.var_points_to t.points_to v

  let assign_ptr_expr t v pt_e =
    { t with points_to = Pt.assign_ptr_expr t.points_to v pt_e }

  let meet_btcons : t -> btcons -> t = fun t c ->
    let cn = abs_eval_btcons t c in
    let dcn = AbsNum.downgrade cn in

    apply (AbsNum.R.meet cn) (AbsNum.NR.meet dcn) (fun x -> x) t

  let unify : t -> t -> t = fun t t' ->
    { bool = unify_map t.bool t'.bool;
      init = eunify_map t.init t'.init;
      num = AbsNum.R.unify t.num t'.num;
      points_to = Pt.unify t.points_to t'.points_to }

  let change_environment : t -> mvar list -> t = fun t l ->
    let l = u8_blast_vars ~blast_arrays:true l in
    let bvars = bool_vars l
    and ivars = init_vars l in
    (* We remove the variables that are not in l *)
    let b = Mbv.filter (fun s _ -> List.mem s bvars) t.bool
    and init = EMs.kfilter (fun s -> List.mem s ivars) t.init in

    (* (\* We add the variables that are in l but not in t.bool's domain.
     *    We do not need to do it for t.init, since it is lazily populated *\)
     * let b = List.fold_left (fun b s ->
     *     if Mbv.mem s b then b
     *     else Mbv.add s (AbsNum.downgrade t.num) b) b bvars in *)

    (* We change the environment of the underlying numerical domain *)
    let f x = AbsNum.R.change_environment x l
    and df x = AbsNum.NR.change_environment x l in
    apply f df (fun x -> x) { t with bool = b; init = init }

  let remove_vars : t -> mvar list -> t = fun t l ->
    let l = u8_blast_vars ~blast_arrays:true l in
    let bvars = bool_vars l
    and ivars = init_vars l in
    (* We remove the variables in l *)
    let b = Mbv.filter (fun s _ -> not (List.mem s bvars)) t.bool
    and init = EMs.kfilter (fun s -> not (List.mem s ivars)) t.init in

    (* We change the environment of the underlying numerical domain *)
    let f x = AbsNum.R.remove_vars x l
    and df x = AbsNum.NR.remove_vars x l
    and ptf x = Pt.forget_list x l in
    apply f df ptf { t with bool = b; init = init }

  let top_ni : t -> t = fun t ->
    let top = AbsNum.R.top_no_disj t.num in
    let bmap = Mbv.map (fun v -> AbsNum.NR.top v) t.bool in
    { bool = bmap;
      init = EMs.empty;
      num = top;
      points_to = Pt.make [] }

  let to_shape t shp =
    { t with num = AbsNum.R.to_shape t.num shp.num }

  let remove_disj t =
    { t with num = AbsNum.R.remove_disj t.num }

  (* Initialize some variable. 
     Note that an array is always initialized, even if its elements are not
     initialized. *)
  let is_init t at =
    let vats = match at with
      | Aarray _ -> []
      | _ -> u8_blast_at ~blast_arrays:true at in
    let vats = List.map string_of_mvar vats in
    
    { t with
      init = EMs.adds vats (AbsNum.R.bottom t.num |> AbsNum.downgrade) t.init }
    
  (* Copy some variable initialization.
     We only need this for elementary array elements. *)
  let copy_init t l e = match l, e with
    | Mvalue (AarrayEl (_, U8, _)),
      Mvalue (AarrayEl (_, U8, _)) ->
      let l = string_of_mvar l
      and e = string_of_mvar e in
      begin match EMs.find e t.init with
        | x -> { t with init = EMs.adds [l] x t.init }
        | exception Not_found -> t end
    | _ -> assert false
  
  (* Check that a variable is initialized. 
     Note that in Jasmin, an array is always initialized, even if its elements 
     are not initialized. *)
  let check_init : t -> atype -> bool = fun t at ->
    let vats = match at with
      | Aarray _ -> []
      | _ -> u8_blast_at ~blast_arrays:false at |> List.map string_of_mvar in    
    let dnum = AbsNum.downgrade t.num in
    let check x =
      try AbsNum.NR.meet dnum (EMs.find x t.init) |> AbsNum.NR.is_bottom with
      | Not_found -> AbsNum.R.is_bottom t.num in

    List.for_all check vats

  let get_env : t -> Environment.t = fun t -> AbsNum.R.get_env t.num

  let print_init fmt t = match Aparam.is_init_no_print with
    | Aparam.IP_None -> Format.fprintf fmt ""
    | Aparam.IP_All | Aparam.IP_NoArray ->
      let keep s =
        match mvar_of_svar s with
        | Mvalue (AarrayEl _)
          when Aparam.is_init_no_print = Aparam.IP_NoArray -> false
        | _ -> true
      in
      
      let dnum = AbsNum.downgrade t.num in
      let check' a =
        try AbsNum.NR.meet dnum a |> AbsNum.NR.is_bottom with
        | Not_found -> AbsNum.R.is_bottom t.num in

      let m = EMs.map (fun a -> check' a) t.init in
      Format.fprintf fmt "@[<h 2>* Init:@;";
      EMs.iter (fun s b ->
          if b && keep s then Format.fprintf fmt "%s@ " s else ()) m;
      Format.fprintf fmt "@]@;"

  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt t ->
    let print_init fmt = print_init fmt t in

    let print_bool fmt =
      if Aparam.bool_no_print then 
        Format.fprintf fmt ""
      else begin
        Format.fprintf fmt "@[<v 0>* Bool:@;";
        Mbv.iter (fun bv nrval ->
            Format.fprintf fmt "@[<v 2>%a@;%a@]@;" Bvar.print bv
              (AbsNum.NR.print ~full:true) nrval;
          ) t.bool;
        Format.fprintf fmt "@]@;>" 
      end in

    let bool_size = Mbv.cardinal t.bool
    and init_size = EMs.csize t.init in
    let bool_nr_vars =  
      Mbv.fold (fun _ nrd size -> 
          size + Environment.size (AbsNum.NR.get_env nrd))
        t.bool 0
      |> EMs.cfold (fun nrd size -> 
          size + Environment.size (AbsNum.NR.get_env nrd))
        t.init in
    let print_bool_nums fmt = 
      Format.fprintf fmt "* Bool (%d vars.) + Init (%d vars): \
                          total of %d num. vars."
        bool_size init_size bool_nr_vars in

    if !only_rel_print then
      Format.fprintf fmt "@[<v 0>%a@]"
        (AbsNum.R.print ~full:full) t.num
    else
      Format.fprintf fmt "@[<v 0>@[<v 0>%a@]%a@;%t@;%t%t@]@;"
        (AbsNum.R.print ~full:full) t.num
        Pt.print t.points_to
        print_bool_nums
        print_bool
        print_init

  let new_cnstr_blck t l = { t with num = AbsNum.R.new_cnstr_blck t.num l }

  let add_cnstr t ~meet c i =
    let tl, tr = AbsNum.R.add_cnstr t.num ~meet c i in
    ( { t with num = tl }, { t with num = tr } )

  let pop_cnstr_blck t l = { t with num = AbsNum.R.pop_cnstr_blck t.num l }

  let pop_all_blcks t = { t with num = AbsNum.R.pop_all_blcks t.num }
end

module AbsDomMake2 (PW : ProgWrap) : sig
  module AbsDomStd : AbsNumBoolType
  module AbsDomSpc : AbsNumBoolType

  val lift : AbsDomStd.t -> AbsDomSpc.t

  val print :
    print_spc:bool -> Format.formatter ->
    (AbsDomStd.t * AbsDomSpc.t * AbsDomSpc.t) -> unit
end = struct
  module AbsDomMake (PW : ProgWrap) =
    AbsBoolNoRel (AbsNumTMake (PW)) (PointsToImpl)
      
  module AbsDomStd = AbsDomMake (PW)

  module AbsDomSpc = AbsDomMake (PW)

  let () = AbsDomStd.init_is_spec false
  let () = AbsDomSpc.init_is_spec true

  (* We remove all termination-related values (i.e. MNumInv). *)
  let lift (x : AbsDomStd.t) : AbsDomSpc.t =
    let env = AbsDomStd.get_env x in
    let vars = fst (Environment.vars env) in
    let rem = Array.to_list vars
              |> List.filter_map (fun v ->
                  match mvar_of_avar v with
                  | MNumInv _ as mv -> Some mv
                  | _ -> None) in    
    AbsDomStd.remove_vars x rem

    
  let print ~print_spc fmt (std,spc,dead_spc) =
    if not print_spc then
      AbsDomStd.print ~full:true fmt std
    else
      Format.eprintf "@[<v 0>\
                      [* Standard semantics *]@;@[<v 0>%a@]\
                      [* Speculative semantics (live) *]@;@[<v 0>%a@]\
                      [* Speculative semantics (dead) *]@;@[<v 0>%a@]@;\
                      @]%!"
        (AbsDomStd.print ~full:true) std
        (AbsDomSpc.print ~full:true) spc
        (AbsDomSpc.print ~full:true) dead_spc
end  


(**********************)
(* Typing Environment *)
(**********************)

module Ss = Set.Make(Scmp)

module Tcmp = struct
  type t = ty
  let compare = compare
end

module Mty = Map.Make (Tcmp)

type s_env = { s_glob : (string * Type.stype) Ms.t;
               m_locs : mem_loc list }

let pp_s_env fmt env =
  Format.printf fmt "@[<v>global variables:@;%a@]"
    (pp_list (fun fmt (_,(x,sw)) ->
         Format.fprintf fmt "@[%s: %a@]@,"
           x Printer.pp_ty (Conv.ty_of_cty sw)))
    (Ms.bindings env.s_glob)
    (pp_list (fun fmt i -> Format.fprintf fmt "%d" i))

let add_glob env x ws =
  let ty = Bty (U ws) in
  { env with s_glob = Ms.add x (x,Conv.cty_of_ty ty) env.s_glob }


let add_glob_var s v =
  let uv = L.unloc v in
  match uv.v_kind, uv.v_ty with
  | Global, Bty (U _) -> Ms.add uv.v_name (uv.v_name, Conv.cty_of_ty uv.v_ty) s
  | _ -> s

let rec add_glob_expr s = function
  | Pconst _ | Pbool _ | Parr_init _ -> s
  | Pglobal (sw,x) ->
    let ty = Bty (U sw) in
    Ms.add x (x,Conv.cty_of_ty ty) s
  | Pvar x         -> add_glob_var s x
  | Pget(_,x,e)      -> add_glob_expr (add_glob_var s x) e
  | Pload(_,x,e)   -> add_glob_expr (add_glob_var s x) e
  | Papp1(_, e)    -> add_glob_expr s e
  | Papp2(_,e1,e2) -> add_glob_expr (add_glob_expr s e1) e2
  | PappN (_,es) -> List.fold_left add_glob_expr s es
  | Pif(_,e,e1,e2)   -> add_glob_expr
                        (add_glob_expr
                           (add_glob_expr s e) e1) e2

let add_glob_exprs s es = List.fold_left add_glob_expr s es

let rec add_glob_lv s = function
  | Lnone _      -> s
  | Lvar x       -> add_glob_var s x
  | Lmem (_,x,e)
  | Laset (_,x,e)  -> add_glob_expr (add_glob_var s x) e

let add_glob_lvs s lvs = List.fold_left add_glob_lv s lvs

let rec add_glob_instr s i =
  match i.i_desc with
  | Cassgn(x, _, _, e) -> add_glob_expr (add_glob_lv s x) e
  | Copn(x,_,_,e) -> add_glob_exprs (add_glob_lvs s x) e
  | Cif(e,c1,c2) -> add_glob_body (add_glob_body (add_glob_expr s e) c1) c2
  | Cfor(x,(_,e1,e2), c) ->
    add_glob_body (add_glob_expr (add_glob_expr (add_glob_var s x) e1) e2) c
  | Cwhile(_,c,e,c')    -> add_glob_body (add_glob_expr (add_glob_body s c') e) c
  | Ccall(_,x,_,e) -> add_glob_exprs (add_glob_lvs s x) e

and add_glob_body s c =  List.fold_left add_glob_instr s c

let get_wsize = function
  | Type.Coq_sword sz -> sz
  | _ -> raise (Aint_error "Not a Coq_sword")



(*********************)
(* Safety conditions *)
(*********************)

type safe_cond =
  | Initv of var
  | Initai of var * wsize * expr
  | InBound of int * wsize * expr
  | Valid of wsize * ty gvar * expr
  | NotZero of wsize * expr
  | Termination

let pp_var = Printer.pp_var ~debug:false
let pp_expr = Printer.pp_expr ~debug:false
let pp_ws fmt ws = Format.fprintf fmt "%i" (int_of_ws ws)

let pp_safety_cond fmt = function
  | Initv x -> Format.fprintf fmt "is_init %a" pp_var x
  | Initai(x,ws,e) ->
    Format.fprintf fmt "is_init (w%d)%a.[%a]" (int_of_ws ws) pp_var x pp_expr e
  | NotZero(sz,e) -> Format.fprintf fmt "%a <>%a zero" pp_expr e pp_ws sz
  | InBound(n,ws,e)  ->
    Format.fprintf fmt "in_bound: %a-th block of (U%d) words in array of \
                        length %i U8"
      pp_expr e (int_of_ws ws) n
  | Valid (sz, x, e) ->
    Format.fprintf fmt "is_valid %s + %a W%a" x.v_name pp_expr e pp_ws sz
  | Termination -> Format.fprintf fmt "termination"

type violation_loc =
  | InProg of Prog.L.t
  | InReturn of funname

type sem_kind = 
  | StdSem                      (* Standard semantics *)
  | SpcSem                      (* Speculative semantics *)

type violation = violation_loc * sem_kind * safe_cond

let pp_violation_loc fmt = function
  | InProg loc -> Format.fprintf fmt "%a" L.pp_sloc loc
  | InReturn fn -> Format.fprintf fmt "%s return" fn.fn_name

let pp_sem fmt = function
  | StdSem -> Format.fprintf fmt "standard sem."
  | SpcSem -> Format.fprintf fmt "speculative sem."

let pp_violation fmt (loc,sem,cond) =
  Format.fprintf fmt "[%a] %a: %a"
    pp_sem sem
    pp_violation_loc loc
    pp_safety_cond cond

let pp_violations fmt violations =
  if violations = [] then
    Format.fprintf fmt "@[<v>*** No Safety Violation@;@]"
  else
    Format.fprintf fmt "@[<v 2>*** Safety Violation(s):@;@[<v>%a@]@]"
      (pp_list pp_violation) violations

let sem_compare v v' = match v, v' with
  | StdSem, StdSem -> 0
  | SpcSem, SpcSem -> 0
  | SpcSem, StdSem -> -1
  | StdSem, SpcSem -> 1

let vloc_compare v v' = match v, v' with
  | InReturn fn, InReturn fn' -> Stdlib.compare fn fn'
  | InProg _, InReturn _ -> 1
  | InReturn _, InProg _ -> -1
  | InProg l, InProg l' ->
    Stdlib.compare (fst l.loc_start) (fst l'.loc_start)

let rec lex f = match f with
  | f_cmp :: f_t ->
    let c = f_cmp () in
    if c = 0
    then lex f_t
    else c
  | _ -> 0

let v_compare (loc,sem,c) (loc',sem',c') =
  lex [(fun () -> vloc_compare loc loc');
       (fun () ->  sem_compare sem sem');
       (fun () ->  Stdlib.compare c c')]

let add64 x e = Papp2 (E.Oadd ( E.Op_w U64), Pvar x, e)

let in_bound x ws e =
  match (L.unloc x).v_ty with
  | Arr(ws',n) -> [InBound(n * int_of_ws ws' / 8, ws, e)]
  | Bty (U _)-> []                   (* TODO: check this *)
  | _ -> assert false


let init_get x ws e =
  match (L.unloc x).v_ty with
  | Arr _ -> [Initai(L.unloc x, ws, e)]
  | Bty (U _)-> [Initv (L.unloc x)] (* TODO: check this *)
  | _ -> assert false


let safe_op2 e2 = function
  | E.Oand | E.Oor | E.Oadd _ | E.Omul _ | E.Osub _
  | E.Oland _ | E.Olor _ | E.Olxor _
  | E.Olsr _ | E.Olsl _ | E.Oasr _
  | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ -> []

  | E.Odiv E.Cmp_int -> []
  | E.Omod Cmp_int  -> []
  | E.Odiv (E.Cmp_w(_, s)) -> [NotZero (s, e2)]
  | E.Omod (E.Cmp_w(_, s)) -> [NotZero (s, e2)]

  | E.Ovadd _ | E.Ovsub _ | E.Ovmul _
  | E.Ovlsr _ | E.Ovlsl _ | E.Ovasr _ -> []

let safe_var x = match (L.unloc x).v_ty with
  | Arr _ -> []
  | _ -> [Initv(L.unloc x)]

let rec safe_e_rec safe = function
  | Pconst _ | Pbool _ | Parr_init _ | Pglobal _ -> safe
  | Pvar x -> safe_var x @ safe

  | Pload (ws,x,e) -> Valid (ws, L.unloc x, e) :: safe_e_rec safe e
  | Pget (ws, x, e) -> (in_bound x ws e) @ (init_get x ws e) @ safe
  | Papp1 (_, e) -> safe_e_rec safe e
  | Papp2 (op, e1, e2) -> safe_op2 e2 op @ safe_e_rec (safe_e_rec safe e1) e2
  | PappN (E.Opack _,_) -> safe

  | Pif  (_,e1, e2, e3) ->
    (* We do not check "is_defined e1 && is_defined e2" since
        (safe_e_rec (safe_e_rec safe e1) e2) implies it *)
    safe_e_rec (safe_e_rec (safe_e_rec safe e1) e2) e3

let safe_e = safe_e_rec []

let safe_es = List.fold_left safe_e_rec []

let safe_lval = function
  | Lnone _ | Lvar _ -> []
  | Lmem(ws, x, e) -> Valid (ws, L.unloc x, e) :: safe_e_rec [] e
  | Laset(ws,x,e) -> (in_bound x ws e) @ safe_e_rec [] e

let safe_lvals = List.fold_left (fun safe x -> safe_lval x @ safe) []

let safe_opn safe opn es = 
  let id = Expr.get_instr opn in
  List.map (fun c ->
      match c with
      | X86_decl.NotZero(sz, i) ->
        NotZero(sz, List.nth es (Conv.int_of_nat i))) id.i_safe @ safe

let safe_instr ginstr = match ginstr.i_desc with
  | Cassgn (lv, _, _, e) -> safe_e_rec (safe_lval lv) e
  | Copn (lvs,_,opn,es) -> safe_opn (safe_lvals lvs @ safe_es es) opn es
  | Cif(e, _, _) -> safe_e e
  | Cwhile(_,_, _, _) -> []       (* We check the while condition later. *)
  | Ccall(_, lvs, _, es) -> safe_lvals lvs @ safe_es es
  | Cfor (_, (_, e1, e2), _) -> safe_es [e1;e2]

let safe_return main_decl =
  List.fold_left (fun acc v -> safe_var v @ acc) [] main_decl.f_ret


(*********)
(* Utils *)
(*********)

let pcast ws e = match ty_expr e with
  | Bty Int -> Papp1 (E.Oword_of_int ws, e)
  | Bty (U ws') ->
    assert (int_of_ws ws' <= int_of_ws ws);
    if ws = ws' then e
    else Papp1 (E.Ozeroext (ws,ws'), e)

  | Bty Bool | Arr _ -> assert false


let obind2 f x y = match x, y with
  | Some u, Some v -> f u v
  | _ -> None

let mvar_of_var v = match v.v_ty with
  | Bty _ -> Mvalue (Avar v)
  | Arr _ -> Mvalue (Aarray v)

let wsize_of_ty ty = match ty with
  | Bty Bool -> assert false
  | Bty Int -> -1
  | Bty (U sz) -> int_of_ws sz
  | Arr (sz, _) -> int_of_ws sz

let rec combine3 l1 l2 l3 = match l1,l2,l3 with
  | h1 :: t1, h2 :: t2, h3 :: t3 -> (h1,h2,h3) :: combine3 t1 t2 t3
  | [], [], [] -> []
  | _ -> raise (Invalid_argument "combine3")

let rec add_offsets assigns = match assigns with
  | [] -> []
  | (Mvalue (Avar v)) :: tail ->
    (Mvalue (Avar v)) :: (MvarOffset v) :: add_offsets tail
  | u :: tail -> u :: add_offsets tail

let rec add_offsets3 assigns = match assigns with
  | [] -> []
  | (ty, Mvalue (Avar v),es) :: tail ->
    (ty, Mvalue (Avar v),es)
    :: (ty, MvarOffset v,es)
    :: add_offsets3 tail
  | u :: tail -> u :: add_offsets3 tail

let fun_locals ~expand_arrays f_decl =
  let locals = Sv.elements (locals f_decl) in
  let vars =
    List.map mvar_of_var locals
    |> add_offsets in

  if expand_arrays
  then expand_arr_vars vars
  else vars


let fun_args_no_offset f_decl = List.map mvar_of_var f_decl.f_args

let fun_args ~expand_arrays f_decl =
  let args = fun_args_no_offset f_decl
             |> add_offsets in
  if expand_arrays
  then expand_arr_vars args
  else args

let in_cp_var v = match v with
  | Mvalue (Avar v) -> Some (MinValue v)
  | _ -> None

let fun_in_args_no_offset f_decl =
  fun_args_no_offset f_decl |> List.map in_cp_var

let fun_rets_no_offsets f_decl =
  List.map (fun x -> L.unloc x |> mvar_of_var) f_decl.f_ret

let get_mem_range env = List.map (fun x -> MmemRange x) env.m_locs

let prog_globals ~expand_arrays env =
  let vars =
    List.map (fun (_,(s,ty)) -> Mglobal (s, Conv.ty_of_cty ty))
      (Ms.bindings env.s_glob)
    @ get_mem_range env
    |> add_offsets in

  if expand_arrays
  then expand_arr_vars vars
  else vars

let fun_vars ~expand_arrays f_decl env =
  fun_args ~expand_arrays:expand_arrays f_decl
  @ prog_globals ~expand_arrays:expand_arrays env
  @ fun_locals ~expand_arrays:expand_arrays f_decl


(****************************)
(* Expression Linearization *)
(****************************)

let op1_to_abs_unop op1 = match op1 with
  | E.Oneg _   -> Some Texpr1.Neg
  | E.Oword_of_int _ | E.Oint_of_word _ | E.Ozeroext _ -> assert false
  | _ -> None


type abs_binop =
  | AB_Unknown
  | AB_Arith of Apron.Texpr1.binop
  | AB_Shift of [`Unsigned_left | `Unsigned_right | `Signed_right ]
  (* Remark: signed left is a synonymous for unsigned left *)               

let abget = function AB_Arith a -> a | _ -> assert false
  
let op2_to_abs_binop op2 = match op2 with
  | E.Oadd _ -> AB_Arith Texpr1.Add
  | E.Omul _ -> AB_Arith Texpr1.Mul                  
  | E.Osub _ -> AB_Arith Texpr1.Sub

  | E.Omod (Cmp_w (Signed, _)) -> AB_Unknown
  | E.Omod _ -> AB_Arith Texpr1.Mod

  | E.Odiv (Cmp_w (Signed, _)) -> AB_Unknown
  | E.Odiv _ -> AB_Arith Texpr1.Div

  | E.Olsr _ -> AB_Shift `Unsigned_right
  | E.Olsl _ -> AB_Shift `Unsigned_left
  | E.Oasr _ -> AB_Shift `Signed_right
      
  | E.Oand | E.Oor
  | E.Oland _ | E.Olor _ | E.Olxor _ (* bit-wise boolean connectives *)
  | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ -> AB_Unknown

  | E.Ovadd (_, _) | E.Ovsub (_, _) | E.Ovmul (_, _)
  | E.Ovlsr (_, _) | E.Ovlsl (_, _) | E.Ovasr (_, _) -> AB_Unknown


(* Return lin_expr mod 2^n *)
let expr_pow_mod apr_env n lin_expr =
  let mod_expr = cst_pow_minus apr_env n 0 in
  Mtexpr.binop Texpr1.Mod lin_expr mod_expr

let word_interval sign ws = match sign with
  | Signed ->
    let pow_m_1 = mpq_pow (ws - 1) in
    let up_mpq = Mpqf.sub pow_m_1 (Mpqf.of_int 1)         
    and down_mpq = Mpqf.neg pow_m_1 in
    Interval.of_mpqf down_mpq up_mpq 

  | Unsigned ->
    let up_mpq = mpq_pow_minus ws 1 in
    Interval.of_mpqf (Mpqf.of_int 0) up_mpq

(* We wrap expr as an out_i word.
   On signed words: ((((lin_expr - 2^(n-1)) % 2^n) + 2^n) % 2^n) - 2^(n-1)
   On unsigned word:  ((lin_expr            % 2^n) + 2^n) % 2^n)             
*)
let wrap_lin_expr sign n expr =
  let env = Mtexpr.(expr.env) in
  match sign with
  | Signed -> 
    let pow_n = cst_pow_minus env n 0 in
    let pow_n_minus_1 = cst_pow_minus env (n - 1) 0 in

    let expr = Mtexpr.binop Texpr1.Sub expr pow_n_minus_1 in
    let expr = expr_pow_mod env n expr in
    let expr = Mtexpr.binop Texpr1.Add expr pow_n in
    let expr = expr_pow_mod env n expr in
    Mtexpr.binop Texpr1.Sub expr pow_n_minus_1 

  | Unsigned ->
    let pow_n = cst_pow_minus env n 0 in
    
    let expr = expr_pow_mod env n expr in
    let expr = Mtexpr.binop Texpr1.Add expr pow_n in
    expr_pow_mod env n expr

let print_not_word_expr e =
  Format.eprintf "@[<v>Should be a word expression:@;\
                  @[%a@]@;Type:@;@[%a@]@]@."
    (Printer.pp_expr ~debug:(!Glob_options.debug)) e
    (Printer.pp_ty) (Conv.ty_of_cty (Conv.cty_of_ty (ty_expr e)))

let check_is_int v = match v.v_ty with
  | Bty Int -> ()
  | _ ->
    Format.eprintf "%s should be an int but is a %a@."
      v.v_name Printer.pp_ty v.v_ty;
    raise (Aint_error "Bad type")

let check_is_word v = match v.v_ty with
  | Bty (U _) -> ()
  | _ ->
    Format.eprintf "%s should be a word but is a %a@."
      v.v_name Printer.pp_ty v.v_ty;
    raise (Aint_error "Bad type")


(***************)
(* Left Values *)
(***************)

type mlvar =
  | MLnone
  | MLvar of mvar
  | MLvars of mvar list       (* If there is uncertainty on the lvalue where 
                                 the assignement takes place. *)

let pp_mlvar fmt = function
  | MLnone -> Format.fprintf fmt "MLnone"
  | MLvar mv -> Format.fprintf fmt "MLvar %a" pp_mvar mv
  | MLvars mvs ->
    Format.fprintf fmt "MLvars @[<hov 2>%a@]"
      (pp_list pp_mvar) mvs

let mvar_of_lvar_no_array lv = match lv with
  | Lnone _ -> MLnone
  | Lmem _ -> MLnone
  | Lvar x  ->
    let ux = L.unloc x in
    begin match ux.v_kind, ux.v_ty with
      | Global,_ -> assert false (* this case should not be possible *)
      (* MLvar (Mglobal (ux.v_name,ux.v_ty)) *)
      | _, Bty _ -> MLvar (Mvalue (Avar ux))
      | _, Arr _ -> MLvar (Mvalue (Aarray ux)) end
  | Laset _ -> assert false



(*********************)
(* Abstract Iterator *)
(*********************)

(* Locations of the abstract iterator *)
type it_loc =
  | ItFunIn of funname * L.t   (* call-site sensitive function call *)

module ItKey = struct
  type t = it_loc

  let compare it it' = match it, it' with
    | ItFunIn (fn,l), ItFunIn (fn',l') ->
      match Prog.F.compare fn fn' with
      | 0 -> Stdlib.compare l l'
      | _ as res -> res
end

module ItMap = Map.Make(ItKey)


(***********************************)
(* Abstract Expression Interpreter *)
(***********************************)

(* Builds and check properties of expressions for the abstract domain
   [AbsDom], which can be standard of speculative semantics. *)
module AbsExpr (AbsDom : AbsNumBoolType) = struct
  (* Return true iff the linear expression overflows *)
  let linexpr_overflow abs lin_expr sign ws =
    let int = AbsDom.bound_texpr abs lin_expr in
    let ws_int = word_interval sign ws in

    not (Interval.is_leq int ws_int)

  let wrap_if_overflow abs e sign ws =
    if linexpr_overflow abs e sign ws then
      wrap_lin_expr sign ws e
    else e

  (* Casting: lin_expr is a in_i word, and we cast it as an out_i word. *)
  let cast_if_overflows abs out_i in_i lin_expr =
    assert ((out_i <> -1)  && (in_i <> -1));
    if out_i <= in_i then
      wrap_if_overflow abs lin_expr Unsigned out_i
    else
      wrap_if_overflow abs lin_expr Unsigned in_i

  let aeval_cst_var abs x =
    let int = AbsDom.bound_variable abs (mvar_of_var (L.unloc x)) in
    interval_to_int int

  (* Try to evaluate e to a constant expression in abs *)
  let rec aeval_cst_int abs e = match e with
    | Pvar x -> begin match (L.unloc x).v_ty with
        | Bty Int -> aeval_cst_var abs x
        | Bty (U ws) ->
          let env = AbsDom.get_env abs in
          let line = Mtexpr.var env (mvar_of_var (L.unloc x)) in
          if linexpr_overflow abs line Unsigned (int_of_ws ws) then None
          else aeval_cst_var abs x
        | _ -> raise (Aint_error "type error in aeval_cst_int") end

    | Pconst c -> Some (B.to_int c)

    | Papp1 (E.Oneg Op_int, e) ->
      obind (fun x -> Some (- x)) (aeval_cst_int abs e)

    | Papp1 (E.Oint_of_word _, e) ->
      obind (fun x -> Some x) (aeval_cst_int abs e)
    (* No need to check for overflows because we do not allow word operations. *)

    | Papp2 (Oadd Op_int, e1, e2) ->
      obind2 (fun x y -> Some (x + y))
        (aeval_cst_int abs e1) (aeval_cst_int abs e2)

    | Papp2 (Osub Op_int, e1, e2) ->
      obind2 (fun x y -> Some (x - y))
        (aeval_cst_int abs e1) (aeval_cst_int abs e2)

    | Papp2 (Omul Op_int, e1, e2) ->
      obind2 (fun x y -> Some (x * y))
        (aeval_cst_int abs e1) (aeval_cst_int abs e2)

    | _ -> None

  (* Try to evaluate e to a constant expression (of type word) in abs.
     Superficial checks only. *)
  let rec aeval_cst_w abs e = match e with
    | Pvar x -> begin match (L.unloc x).v_ty with
        | Bty (U ws) ->
          let env = AbsDom.get_env abs in
          let line = Mtexpr.var env (mvar_of_var (L.unloc x)) in
          if linexpr_overflow abs line Unsigned (int_of_ws ws) then None
          else aeval_cst_var abs x
        | _ -> raise (Aint_error "type error in aeval_cst_w") end

    | Papp1 (E.Oword_of_int ws, e) ->
      let c_e = aeval_cst_int abs e in
      let pws = BatInt.pow 2 (int_of_ws ws) in
      omap (fun c_e -> ((c_e mod pws) + pws) mod pws) c_e

    | _ -> None


  let arr_full_range x =
    List.init
      ((arr_range x) * (arr_size x |> size_of_ws))
      (fun i -> AarrayEl (x, U8, i))

  let abs_arr_range abs x ws ei = match aeval_cst_int abs ei with
    | Some i -> [AarrayEl (x, ws, i)]
    | None -> arr_full_range x

  (* Collect all variables appearing in e. *)
  let ptr_expr_of_expr abs e =
    let exception Expr_contain_load in
    let rec aux acc e = match e with
      | Pbool _ | Parr_init _ | Pconst _ -> acc

      | Pvar x -> mvar_of_var (L.unloc x) :: acc
      | Pglobal (ws,x) -> Mglobal (x,Bty (U ws)) :: acc
      | Pget(ws,x,ei) ->
        (abs_arr_range abs (L.unloc x) ws ei
         |> List.map (fun x -> Mvalue x))
        @ acc

      | Papp1 (_, e1) -> aux acc e1
      | PappN (_, es) -> List.fold_left aux acc es

      | Pload _ -> raise Expr_contain_load

      | Pif (_,_,e1,e2) | Papp2 (_, e1, e2) -> aux (aux acc e1) e2 in

    try PtVars (aux [] e) with Expr_contain_load -> PtTopExpr

  exception Unop_not_supported of E.sop1

  exception Binop_not_supported of E.sop2

  exception If_not_supported

  let top_linexpr abs ws_e =
    let lin = Mtexpr.cst (AbsDom.get_env abs) (Coeff.Interval Interval.top) in
    wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

  let rec linearize_iexpr abs (e : expr) =
    let apr_env = AbsDom.get_env abs in
    match e with
    | Pconst z -> mtexpr_of_bigint apr_env z

    | Pvar x ->
      check_is_int (L.unloc x);
      Mtexpr.var apr_env (Mvalue (Avar (L.unloc x)))

    | Papp1(E.Oint_of_word sz,e1) ->
      assert (ty_expr e1 = tu sz);
      let abs_expr1 = linearize_wexpr abs e1 in
      wrap_if_overflow abs abs_expr1 Unsigned (int_of_ws sz)

    | Papp1 (op1, e1) ->
      begin match op1_to_abs_unop op1 with
        | Some absop ->
          Mtexpr.unop absop (linearize_iexpr abs e1)

        | None -> raise (Unop_not_supported op1) end

    | Papp2 (op2, e1, e2) ->
      begin match op2_to_abs_binop op2 with
        | AB_Arith absop ->
          Mtexpr.(binop absop
                    (linearize_iexpr abs e1)
                    (linearize_iexpr abs e2))

        | AB_Unknown -> raise (Binop_not_supported op2)
        | AB_Shift _ -> assert false (* shift only makes sense on bit-vectors *)
      end

    | Pif _ -> raise If_not_supported

    | _ -> assert false

  and linearize_wexpr abs (e : ty gexpr) =
    let apr_env = AbsDom.get_env abs in
    let ws_e = ws_of_ty (ty_expr e) in

    match e with
    | Pvar x ->
      check_is_word (L.unloc x);
      let lin = Mtexpr.var apr_env (Mvalue (Avar (L.unloc x))) in
      wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

    | Pglobal(ws, x) ->
      let lin = Mtexpr.var apr_env (Mglobal (x,Bty (U ws))) in
      wrap_if_overflow abs lin Unsigned (int_of_ws ws)

    | Papp1(E.Oword_of_int sz,e1) ->
      assert (ty_expr e1 = tint);
      let abs_expr1 = linearize_iexpr abs e1 in
      wrap_if_overflow abs abs_expr1 Unsigned (int_of_ws sz)

    | Papp1(E.Ozeroext (osz,isz),e1) ->
      assert (ty_expr e1 = tu isz);
      let abs_expr1 = linearize_wexpr abs e1 in
      cast_if_overflows abs (int_of_ws osz) (int_of_ws isz) abs_expr1

    | Papp1 (op1, e1) ->
      begin match op1_to_abs_unop op1 with
        | Some absop ->
          let lin = Mtexpr.unop absop (linearize_wexpr abs e1) in
          wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

        | None -> raise (Unop_not_supported op1) end

    | Papp2 (op2, e1, e2) ->
      begin match op2_to_abs_binop op2 with
        | AB_Arith Texpr1.Mod
        | AB_Arith Texpr1.Add
        | AB_Arith Texpr1.Mul
        | AB_Arith Texpr1.Sub as absop->
          let lin = Mtexpr.(binop (abget absop)
                              (linearize_wexpr abs e1)
                              (linearize_wexpr abs e2)) in
          wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

        | AB_Shift `Signed_right
        | AB_Arith Texpr1.Div
        | AB_Arith Texpr1.Pow
        | AB_Unknown ->
          raise (Binop_not_supported op2)

        | AB_Shift stype  -> match aeval_cst_w abs e2 with
          | Some i when i <= int_of_ws ws_e ->
            let absop = match stype with
              | `Unsigned_right -> Texpr1.Div
              | `Unsigned_left -> Texpr1.Mul
              | _ -> assert false in
            let lin = Mtexpr.(binop absop
                                (linearize_wexpr abs e1)
                                (cst_pow_minus apr_env i 0)) in

            wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)

          | _ ->
            raise (Binop_not_supported op2)
      end

    | Pget(ws,x,ei) ->
      begin match abs_arr_range abs (L.unloc x) ws ei with
        | [] -> assert false
        | [at] ->
          let lin = Mtexpr.var apr_env (Mvalue at) in
          wrap_if_overflow abs lin Unsigned (int_of_ws ws_e)
        | _ -> top_linexpr abs ws_e end

    (* We return top on loads and Opack *)
    | PappN (E.Opack _, _) | Pload _ -> top_linexpr abs ws_e

    | _ -> print_not_word_expr e;
      assert false

  let map_f f e_opt = match e_opt with
    | None -> None
    | Some (ty,b,el,er) -> Some (ty, b, f el, f er)

  let rec remove_if_expr_aux : 'a Prog.gexpr ->
    ('a * 'a Prog.gexpr * 'a Prog.gexpr * 'a Prog.gexpr) option = function
    | Pif (ty,e1,et,ef) -> Some (ty,e1,et,ef)

    | Pconst _  | Pbool _ | Parr_init _ | Pvar _ | Pglobal _ -> None

    | Pget(ws,x,e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Pget(ws,x,ex))

    | Pload (sz, x, e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Pload (sz,x,ex))

    | Papp1 (op1, e1) ->
      remove_if_expr_aux e1
      |> map_f (fun ex -> Papp1 (op1,ex))

    | Papp2 (op2, e1, e2) ->
      begin match remove_if_expr_aux e1 with
        | Some _ as e_opt -> map_f (fun ex -> Papp2 (op2, ex, e2)) e_opt
        | None -> remove_if_expr_aux e2
                  |> map_f (fun ex -> Papp2 (op2, e1, ex)) end

    | PappN (opn, es) ->
      let rec f_expl i es = match es with
        | [] -> (-1,None)
        | e :: r_es -> match remove_if_expr_aux e with
          | None -> f_expl (i + 1) r_es
          | Some _ as r -> (i,r) in

      match f_expl 0 es with
      | _,None -> None
      | i,Some (ty, b, el, er) ->
        let repi ex = List.mapi (fun j x -> if j = i then ex else x) es in
        Some (ty, b, PappN (opn, repi el), PappN (opn, repi er))


  let rec remove_if_expr (e : 'a Prog.gexpr) = match remove_if_expr_aux e with
    | Some (_,b,el,er) ->
      List.map (fun (l_bool,expr) ->
          (b :: l_bool,expr))
        (remove_if_expr el)
      @ (List.map (fun (l_bool,expr) ->
          ((Papp1 (E.Onot,b)) :: l_bool,expr))
          (remove_if_expr er))
    | None -> [([],e)]

  let op2_to_typ op2 =
    let to_cmp_kind = function
      | E.Op_int -> E.Cmp_int
      | E.Op_w ws -> E.Cmp_w (Unsigned, ws) in

    match op2 with
    | E.Oand | E.Oor | E.Oadd _ | E.Omul _ | E.Osub _
    | E.Odiv _ | E.Omod _ | E.Oland _ | E.Olor _
    | E.Olxor _ | E.Olsr _ | E.Olsl _ | E.Oasr _ -> assert false

    | E.Oeq k -> (Tcons1.EQ, to_cmp_kind k)
    | E.Oneq k -> (Tcons1.DISEQ, to_cmp_kind k)
    | E.Olt k -> (Tcons1.SUP, k)
    | E.Ole k -> (Tcons1.SUPEQ, k)
    | E.Ogt k -> (Tcons1.SUP, k)
    | E.Oge k -> (Tcons1.SUPEQ, k)

    | Ovadd (_, _) | Ovsub (_, _) | Ovmul (_, _)
    | Ovlsr (_, _) | Ovlsl (_, _) | Ovasr (_, _) -> assert false

  let rec bexpr_to_btcons_aux : AbsDom.t -> 'a Prog.gexpr -> btcons =
    fun abs e ->
    let aux = bexpr_to_btcons_aux abs in
    match e with
    | Pbool b ->
      let cons =
        if b then true_tcons1 (AbsDom.get_env abs)
        else false_tcons1 (AbsDom.get_env abs) in
      BLeaf cons

    | Pvar x -> BVar (Bvar.make (Mvalue (Avar (L.unloc x))) true)

    | Pglobal _ -> assert false (* Global variables are of type word *)

    | Pif(_,e1,et,ef) ->
      let bet, bef, be1 = aux et, aux ef, aux e1 in
      let be1_f = match flip_btcons be1 with
        | Some c -> c
        | None -> raise Bop_not_supported in

      BOr ( BAnd(be1,bet), BAnd(be1_f,bef) )

    | Papp1 (op1, e1) -> begin match op1 with
        | E.Onot ->
          let be1 = aux e1 in
          begin match flip_btcons be1 with
            | Some c -> c
            | None -> raise Bop_not_supported end
        | _ -> assert false end

    | Papp2 (op2, e1, e2) -> begin match op2 with
        | E.Oadd _ | E.Omul _ | E.Osub _
        | E.Odiv _ | E.Omod _ | E.Oland _ | E.Olor _
        | E.Olxor _ | E.Olsr _ | E.Olsl _ | E.Oasr _ -> assert false

        | Ovadd (_, _) | Ovsub (_, _) | Ovmul (_, _)
        | Ovlsr (_, _) | Ovlsl (_, _) | Ovasr (_, _) -> assert false

        | E.Oand -> BAnd ( aux e1, aux e2 )

        | E.Oor -> BOr ( aux e1, aux e2 )

        | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ ->
          match remove_if_expr_aux e with
          | Some (ty,eb,el,er)  -> aux (Pif (ty,eb,el,er))
          | None -> flat_bexpr_to_btcons abs op2 e1 e2 end

    | _ -> assert false

  and flat_bexpr_to_btcons abs op2 e1 e2 =
    let e1',e2' = swap_op2 op2 e1 e2 in
    let lincons, cmp_kind = op2_to_typ op2 in

    (* (Sub lin2 lin1) lincos 0  *)
    try let lin2,lin1 = match cmp_kind with
        | E.Cmp_int ->
          let lin1 = linearize_iexpr abs e1'
          and lin2 = linearize_iexpr abs e2' in
          lin2, lin1
        (* Mtexpr.(binop Sub lin2 lin1) *)

        | E.Cmp_w (sign, ws) ->
          let lin1 = match ty_expr e1' with
            | Bty Int   -> linearize_iexpr abs e1'
            | Bty (U _) -> linearize_wexpr abs e1'
            | _ -> assert false
          and lin2 = match ty_expr e2' with
            | Bty Int   -> linearize_iexpr abs e2'
            | Bty (U _) -> linearize_wexpr abs e2'
            | _ -> assert false in

          let lin1 = wrap_if_overflow abs lin1 sign (int_of_ws ws)
          and lin2 = wrap_if_overflow abs lin2 sign (int_of_ws ws) in
          (* Mtexpr.(binop Sub lin2 lin1)  *)
          lin2, lin1
      in

      (* We do some basic simplifications.
         [expr lincons 0] must be equivalent to [(Sub lin2 lin1) lincos 0] *)
      let expr = match lincons, lin2, lin1 with
        | (Tcons1.EQ | Tcons1.DISEQ), { mexpr = Mtexpr.Mcst cst }, lin
        | (Tcons1.EQ | Tcons1.DISEQ), lin, { mexpr = Mtexpr.Mcst cst } ->      
          if Coeff.equal_int cst 0
          then lin
          else Mtexpr.(binop Sub lin2 lin1) 
        | _ -> Mtexpr.(binop Sub lin2 lin1) 
      in
      BLeaf (Mtcons.make expr lincons)

    with Unop_not_supported _ | Binop_not_supported _ ->
      raise Bop_not_supported


  let bexpr_to_btcons : 'a Prog.gexpr -> AbsDom.t -> btcons option =
    fun e abs -> try Some (bexpr_to_btcons_aux abs e) with
        Bop_not_supported -> None


  let linearize_if_iexpr : 'a Prog.gexpr -> AbsDom.t -> s_expr =
    fun e abs ->
    List.map (fun (bexpr_list, expr) ->
        let f x = bexpr_to_btcons x abs in
        let b_list = List.map f bexpr_list in

        let b_list =
          if List.exists (fun x -> x = None) b_list then []
          else List.map oget b_list in

        let lin_expr = try Some (linearize_iexpr abs expr) with
          | Unop_not_supported _ | Binop_not_supported _ -> None in

        (b_list, lin_expr))
      (remove_if_expr e)

  let linearize_if_wexpr : int -> ty gexpr -> AbsDom.t -> s_expr =
    fun out_sw e abs ->
    List.map (fun (bexpr_list, expr) ->
        let f x = bexpr_to_btcons x abs in
        let b_list = List.map f bexpr_list in

        let b_list =
          if List.exists (fun x -> x = None) b_list then []
          else List.map oget b_list in

        let in_sw = ws_of_ty (ty_expr e) in

        let lin_expr =
          try linearize_wexpr abs expr
              |> cast_if_overflows abs out_sw (int_of_ws in_sw)
              |> some
          with | Unop_not_supported _ | Binop_not_supported _ -> None in

        (b_list, lin_expr))
      (remove_if_expr e)

  let rec linearize_if_expr : int -> 'a Prog.gexpr -> AbsDom.t -> s_expr =
    fun out_ws e abs ->
    match ty_expr e with
    | Bty Int ->
      assert (out_ws = -1);
      linearize_if_iexpr e abs

    | Bty (U _) -> linearize_if_wexpr out_ws e abs

    | Bty Bool -> assert false
    | Arr _ -> assert false


  let set_zeros f_args abs =
    List.fold_left (fun abs v -> match v with
        | MvarOffset _ | MmemRange _ ->
          let env = AbsDom.get_env abs in
          let z_expr = Mtexpr.cst env (Coeff.s_of_int 0) in
          let z_sexpr = sexpr_from_simple_expr z_expr in

          AbsDom.assign_sexpr ~force:true abs v z_sexpr
        | _ -> abs)
      abs f_args


  let set_bounds f_args abs =
    List.fold_left (fun abs v ->
        let ws = match v with
          | Mvalue (AarrayEl (_,ws,_)) -> Some ws
          | Mvalue (Avar gv) -> begin match gv.v_ty with
              | Bty (U ws) -> Some ws
              | _ -> None end
          | _ -> None in

        if ws <> None then
          let int = word_interval Unsigned (oget ws |> int_of_ws)
          and env = AbsDom.get_env abs in
          let z_sexpr = Mtexpr.cst env (Coeff.Interval int)
                        |> sexpr_from_simple_expr in

          AbsDom.assign_sexpr abs v z_sexpr
        else abs)
      abs f_args


  let apply_glob globs abs =
    List.fold_left (fun abs (ws,n,i) ->
        let env = AbsDom.get_env abs in
        let sexpr = mtexpr_of_bigint env i |> sexpr_from_simple_expr in
        AbsDom.assign_sexpr abs (Mglobal (n, Bty (U ws))) sexpr)
      abs globs


  (*-------------------------------------------------------------------------*)
  (* Return te mvar where the abstract assignment takes place. For now, no
     abstraction of the memory. *)
  let mvar_of_lvar abs lv = match lv with
    | Lnone _ | Lmem _ | Lvar _ -> mvar_of_lvar_no_array lv

    | Laset (ws, x, ei) ->
      match abs_arr_range abs (L.unloc x) ws ei
            |> List.map (fun v -> Mvalue v) with
      | [] -> assert false
      | [mv] -> MLvar (mv)
      | _ as mvs -> MLvars mvs

  let apply_offset_expr abs outmv inv offset_expr =
    match ty_gvar_of_mvar outmv with
    | None -> abs
    | Some outv ->
      let env = AbsDom.get_env abs in
      let inv_os = Mtexpr.var env (MvarOffset inv) in

      let off_e = linearize_wexpr abs offset_expr
      and e_ws = ws_of_ty (ty_expr offset_expr) in
      let wrap_off_e = wrap_if_overflow abs off_e Unsigned (int_of_ws e_ws) in

      let sexpr =
        Mtexpr.binop Texpr1.Add inv_os wrap_off_e
        |> sexpr_from_simple_expr in

      AbsDom.assign_sexpr abs (MvarOffset outv) sexpr

  let aeval_top_offset abs outmv = match ty_gvar_of_mvar outmv with
    | Some outv -> AbsDom.forget_list abs [MvarOffset outv]
    | None -> abs

  let valid_offset_var abs ws_o y =
    if ws_o = Bty (U (U64)) then
      match AbsDom.var_points_to abs (mvar_of_var (L.unloc y)) with
      | TopPtr -> false
      | Ptrs ypts -> List.length ypts = 1
    else false

  (* Evaluate the offset abstraction *)
  let aeval_offset abs ws_o outmv e = match e with
    | Pvar y ->
      if valid_offset_var abs ws_o y then
        apply_offset_expr abs outmv (L.unloc y) (pcast U64 (Pconst(B.of_int 0)))
      else aeval_top_offset abs outmv

    | Papp2 (op2,el,er) -> begin match op2,el with
        | E.Oadd ( E.Op_w U64), Pvar y ->
          if valid_offset_var abs ws_o y then
            apply_offset_expr abs outmv (L.unloc y) er
          else aeval_top_offset abs outmv

        | _ -> aeval_top_offset abs outmv end

    | _ -> aeval_top_offset abs outmv

  (* Initialize variable or array elements. *)
  let a_init_mv_no_array mv abs = match mv with
    |  Mvalue (AarrayEl _ as at) |  Mvalue (Avar _ as at) ->
      AbsDom.is_init abs at
    | _ -> assert false

  (* Initialize variable or array elements lvalues. *)
  let a_init_mlv_no_array mlv abs = match mlv with
    | MLvar mv -> a_init_mv_no_array mv abs
    | _ -> assert false

  (* Array assignment. Does the numerical assignments.
     Remark: array elements do not need to be tracked in the point-to
     abstraction. *)
  let assign_arr_expr a v e =
    match v with
    | Mvalue (Aarray gv) -> begin match Mtexpr.(e.mexpr) with
        | Mtexpr.Mvar (Mvalue (Aarray ge)) ->
          let n = arr_range gv in
          let ws = arr_size gv in
          assert (n = arr_range ge);
          assert (ws = arr_size ge);
          List.fold_left (fun a i ->
              let vi = Mvalue (AarrayEl (gv,ws,i))  in
              let eiv = Mvalue (AarrayEl (ge,ws,i)) in
              let ei = Mtexpr.var (AbsDom.get_env a) eiv
                       |> sexpr_from_simple_expr in

              (* Numerical abstraction *)
              let a = AbsDom.assign_sexpr a vi ei in

              (* Initialization *)
              List.fold_left2 (fun a vi eiv ->
                  AbsDom.copy_init a vi eiv)
                a
                (u8_blast_var ~blast_arrays:true vi)
                (u8_blast_var ~blast_arrays:true eiv))

            a (List.init n (fun i -> i))

        | _ -> assert false end
    | _ -> assert false


  let omvar_is_offset = function
    | MLvar (MvarOffset _) -> true
    | _ -> false

  (* Abstract evaluation of an assignment. 
     Also handles variable initialization. *)
  let abs_assign : AbsDom.t -> 'a gty -> mlvar -> ty gexpr -> AbsDom.t =
    fun abs out_ty out_mvar e ->
      assert (not (omvar_is_offset out_mvar));
      match ty_expr e, out_mvar with
      | _, MLnone -> abs

      (* Here, we have no information on which elements are initialized. *)
      | _, MLvars vs -> AbsDom.forget_list abs vs 

      | Bty Int, MLvar mvar | Bty (U _), MLvar mvar ->
        (* Numerical abstraction *)
        let lv_s = wsize_of_ty out_ty in
        let s_expr = linearize_if_expr lv_s e abs in
        let abs0 = abs in
        let abs = AbsDom.assign_sexpr abs mvar s_expr in

        (* Points-to abstraction *)
        let ptr_expr = ptr_expr_of_expr abs0 e in
        let abs = AbsDom.assign_ptr_expr abs mvar ptr_expr in

        (* Offset abstraction *)
        let abs = aeval_offset abs out_ty mvar e in
        
        a_init_mlv_no_array out_mvar abs

      | Bty Bool, MLvar mvar ->
        begin
          let abs = match bexpr_to_btcons e abs with
            | None -> AbsDom.forget_bvar abs mvar 
            | Some btcons -> AbsDom.assign_bexpr abs mvar btcons in
          a_init_mlv_no_array out_mvar abs
        end

      | Arr _, MLvar mvar ->
        match e with
        | Pvar x ->
          let apr_env = AbsDom.get_env abs in
          let se = Mtexpr.var apr_env (Mvalue (Aarray (L.unloc x))) in
          begin match mvar with
            | Mvalue (Aarray _) -> assign_arr_expr abs mvar se 
            | Temp _ -> assert false (* this case should not be possible *)
            | _ -> assert false end

        | Parr_init _ -> abs

        | _ ->
          Format.eprintf "@[%a@]@." (Printer.pp_expr ~debug:true) e;
          assert false

  let abs_assign_opn abs lvs assgns =
    let abs, mlvs_forget =
      List.fold_left2 (fun (abs, mlvs_forget) lv e_opt ->
          match mvar_of_lvar abs lv, e_opt with
          | MLnone,_ -> (abs, mlvs_forget)

          | MLvar mlv as cmlv, None ->
            (* Remark: n-ary operation cannot return arrays. *)
            let abs = a_init_mlv_no_array cmlv abs in
            (abs, mlv :: mlvs_forget)
          | MLvar mlv, Some e ->
            (abs_assign abs (ty_lval lv) (MLvar mlv) e, mlvs_forget)

          | MLvars mlvs, _ -> (abs, mlvs @ mlvs_forget))
        (abs,[]) lvs assgns in

    let mlvs_forget = List.sort_uniq Stdlib.compare mlvs_forget in

    AbsDom.forget_list abs mlvs_forget 

end


(************************)
(* Abstract Interpreter *)
(************************)

module AbsInterpreter (PW : ProgWrap) : sig
  val analyze : unit -> violation list
                        * (Format.formatter -> unit -> unit)
                        * (Format.formatter -> mvar -> unit)
                        * (Format.formatter -> mvar -> unit)
end = struct

  let main_decl,prog = PW.main, PW.prog;;

  Prof.reset_all ();;


  (*---------------------------------------------------------------*)
  module AbsDom2 = AbsDomMake2 (struct
      let main = main_decl
      let prog = prog
      let param = PW.param
    end)

  (* Abstract domain for the standard semantics. *)
  module AbsDomStd = AbsDom2.AbsDomStd

  (* Abstract domain for the speculative semantics. *)
  module AbsDomSpc = AbsDom2.AbsDomSpc

  let std_to_spc = AbsDom2.lift

  (* Keeps only the program initial values and memory accesses variables. *)
  let spc_to_dead_spc a =
    let env = AbsDomSpc.get_env a in
    let forget_spc = 
      fst (Environment.vars env)
      |> Array.to_list
      |> List.filter_map (fun v ->
          match mvar_of_avar v with
          | Mglobal _ | MinValue _ | MmemRange _ -> None
          | Mvalue _ | MvarOffset _ as mv -> Some mv
          | MNumInv _ | Temp _ | WTemp _ -> assert false) in
    AbsDomSpc.forget_list a forget_spc
    |> AbsDomSpc.pop_all_blcks


  module AbsExprStd = AbsExpr (AbsDomStd)
  module AbsExprSpc = AbsExpr (AbsDomSpc)

  (*---------------------------------------------------------------*)
  type side_effects = mem_loc list

  (* Function abstraction.
     This is a bit messy because the same function abstraction can be used
     with different call-stacks, but the underlying disjunctive domain we 
     use is sensitive to the call-stack. 
     Remark: we cannot analyse function calls under the speculative 
     semantics. *)
  module FAbs : sig
    type t

    (* [make abs_in abs_out f_effects] *)
    val make    : AbsDomStd.t -> AbsDomStd.t -> side_effects -> t

    (* [ apply in fabs = (f_in, f_out, effects) ]:
       Return the abstraction of the initial states that was used, the
       abstract final state, and the side-effects of the function (if the
       abstraction applies in state [in]).
       Remarks: 
       - the final state abstraction [f_out] uses the disjunctions of [in]. *)
    val apply : AbsDomStd.t -> t -> (AbsDomStd.t * side_effects) option

    val get_in : t -> AbsDomStd.t
  end = struct
    (* Sound over-approximation of a function 'f' behavior:
       for any initial state in [it_in], the state after executing the function
       'f' is over-approximated by [it_out], the function's side-effects are at
       most [it_s_effects]. *)
    type t = { fa_in        : AbsDomStd.t;
               fa_out       : AbsDomStd.t;
               fa_s_effects : mem_loc list; }

    let make abs_in abs_out f_effects =
      { fa_in        = AbsDomStd.remove_disj abs_in;
        fa_out       = AbsDomStd.remove_disj abs_out;
        fa_s_effects = f_effects; }

    let apply abs_in fabs =
      if AbsDomStd.is_included abs_in (AbsDomStd.to_shape fabs.fa_in abs_in) 
      then begin
        debug (fun () -> 
            Format.eprintf "Reusing previous analysis of the body ...@.@.");
        Some (AbsDomStd.to_shape fabs.fa_out abs_in, fabs.fa_s_effects)
      end
      else None

    let get_in t = t.fa_in
  end


  (*---------------------------------------------------------------*)
  (* The speculative semantics does not check for termination
     (hence no numerical invariant). 
     [abs_dead_spc] is an abstraction of the memory accesses of the 
     speculative semantics. Its domain is MmemRange x MinValue. *)
  type astate = { it : FAbs.t ItMap.t;
                  abs_std : AbsDomStd.t; (* standard semantics *)
                  abs_spc : AbsDomSpc.t; (* speculative semantics *)
                  abs_dead_spc : AbsDomSpc.t;
                  spec_analysis : bool;  
                  cstack : funname list;
                  env : s_env;
                  prog : unit prog;
                  s_effects : side_effects;
                  violations : violation list }


  (* TODO: get rid of initialization for speculative semantics ? *)
  let init_state_init_args f_args state =
    List.fold_left (fun state v -> match v with
        | Mvalue at ->
          { state with abs_std = AbsDomStd.is_init state.abs_std at;
                       abs_spc = AbsDomSpc.is_init state.abs_spc at; }
        | _ -> state )
      state f_args

  let init_env : 'info prog -> mem_loc list -> s_env =
    fun (glob_decls, fun_decls) mem_locs ->
    let env = { s_glob = Ms.empty; m_locs = mem_locs } in
    let env =
      List.fold_left (fun env (ws, x, _) -> add_glob env x ws)
        env glob_decls in

    List.fold_left (fun env f_decl ->
        { env with s_glob = List.fold_left (fun s_glob ginstr ->
              add_glob_instr s_glob ginstr)
              env.s_glob f_decl.f_body })
      env fun_decls

  let init_state : unit func -> unit prog -> astate =
    fun main_decl (glob_decls, fun_decls) ->
      let mem_locs = List.map (fun x -> MemLoc x) main_decl.f_args in
      let env = init_env (glob_decls, fun_decls) mem_locs in
      let it = ItMap.empty in

      (* We add the initial variables *)
      let f_args = fun_args ~expand_arrays:true main_decl in
      (* If f_args is empty, we add a dummy variable to avoid having an
         empty relational abstraction *)
      let f_args = if f_args = [] then [dummy_mvar] else f_args in

      let f_in_args = List.map in_cp_var f_args
      and m_locs = List.map (fun mloc -> MmemRange mloc ) env.m_locs in

      (* We set the offsets and ranges to zero, and bound the variables using
         their types. E.g. register of type U 64 is in [0;2^64]. *)
      let abs = AbsDomStd.make (f_args @ m_locs) mem_locs
                |> AbsExprStd.set_zeros (f_args @ m_locs)
                |> AbsExprStd.set_bounds f_args in

      (* We apply the global declarations *)
      let abs = AbsExprStd.apply_glob glob_decls abs in

      (* We extend the environment to its local variables *)
      let f_vars = (List.map otolist f_in_args |> List.flatten)
                   @ fun_vars ~expand_arrays:true main_decl env in

      let abs = AbsDomStd.change_environment abs f_vars in

      (* We keep track of the initial values. *)
      let abs = List.fold_left2 (fun abs x oy -> match oy with
          | None -> abs
          | Some y ->
            let sexpr = Mtexpr.var (AbsDomStd.get_env abs) x
                        |> sexpr_from_simple_expr in
            AbsDomStd.assign_sexpr abs y sexpr)
          abs f_args f_in_args in

      (* Initially, the two semantics coincide. *)
      let abs_spc = std_to_spc abs in

      { it = it;
        abs_std = abs;
        abs_spc = abs_spc;
        abs_dead_spc = spc_to_dead_spc abs_spc;
        spec_analysis = true;
        cstack = [main_decl.f_name];
        env = env;
        prog = (glob_decls, fun_decls);
        s_effects = [];
        violations = [] }

      (* We initialize the arguments. Note that for exported function, we 
         know that input arrays are initialized. *)
      |> init_state_init_args (fun_args ~expand_arrays:true main_decl)


  (*-------------------------------------------------------------------------*)
  (* Checks that all safety conditions hold for the standard semantics, except
     for valid memory access. *)
  let is_safe_std state = function
    | Initv v -> begin match mvar_of_var v with
        | Mvalue at -> AbsDomStd.check_init state.abs_std at
        | _ -> assert false end

    | Initai (v,ws,e) -> begin match mvar_of_var v with
        | Mvalue (Aarray v) ->
          let is = AbsExprStd.abs_arr_range state.abs_std v ws e in
          List.for_all (AbsDomStd.check_init state.abs_std) is
        | _ -> assert false end

    | InBound (i,ws,e) ->
      (* We check that (e + 1) * ws/8 is no larger than i *)
      let epp = Papp2 (E.Oadd E.Op_int,
                       e,
                       Pconst (B.of_int 1)) in
      let wse = Papp2 (E.Omul E.Op_int,
                       epp,
                       Pconst (B.of_int ((int_of_ws ws) / 8))) in
      let be = Papp2 (E.Ogt E.Cmp_int, wse, Pconst (B.of_int i)) in

      begin match AbsExprStd.bexpr_to_btcons be state.abs_std with
        | None -> false
        | Some c -> 
          AbsDomStd.is_bottom (AbsDomStd.meet_btcons state.abs_std c) end

    | NotZero (ws,e) ->
      (* We check that e is never 0 *)
      let be = Papp2 (E.Oeq (E.Op_w ws), e, pcast ws (Pconst (B.of_int 0))) in
      begin match AbsExprStd.bexpr_to_btcons be state.abs_std with
        | None -> false
        | Some c -> 
          AbsDomStd.is_bottom (AbsDomStd.meet_btcons state.abs_std c) end

    | Valid _ | Termination -> true (* These are checked elsewhere *)

  (* Update abs with the abstract memory range for memory accesses. *)
  let mem_safety_apply_std (abs, violations, s_effect) = function
    | Valid (ws,x,e) as pv ->
      begin match AbsDomStd.var_points_to abs (mvar_of_var x) with
        | Ptrs pts ->
          if List.length pts = 1 then
            let pt = List.hd pts in
            let x_o = Mtexpr.var (AbsDomStd.get_env abs) (MvarOffset x) in
            let lin_e = AbsExprStd.linearize_wexpr abs e in
            let c_ws =
              ((int_of_ws ws) / 8)
              |> Coeff.s_of_int
              |> Mtexpr.cst (AbsDomStd.get_env abs) in
            let ws_plus_e = Mtexpr.binop Texpr1.Add c_ws lin_e in
            let sexpr = Mtexpr.binop Texpr1.Add x_o ws_plus_e
                        |> sexpr_from_simple_expr in

            ( AbsDomStd.assign_sexpr abs (MmemRange pt) sexpr,
              violations,
              if List.mem pt s_effect then s_effect else pt :: s_effect)
          else (abs, pv :: violations, s_effect)
        | TopPtr -> (abs, pv :: violations, s_effect) end

    | _ -> (abs, violations, s_effect)


  (*-------------------------------------------------------------------------*)
  (* Checks that all safety conditions hold for the speculatieve semantics,
     except for valid memory access. *)
  let is_safe_spc state = function
    (* we do not check initialization for the speculative semantics *)
    | Initv _ | Initai _ -> true 

    | InBound (i,ws,e) ->
      (* We check that (e + 1) * ws/8 is no larger than i *)
      let epp = Papp2 (E.Oadd E.Op_int,
                       e,
                       Pconst (B.of_int 1)) in
      let wse = Papp2 (E.Omul E.Op_int,
                       epp,
                       Pconst (B.of_int ((int_of_ws ws) / 8))) in
      let be = Papp2 (E.Ogt E.Cmp_int, wse, Pconst (B.of_int i)) in

      begin match AbsExprSpc.bexpr_to_btcons be state.abs_spc with
        | None -> false
        | Some c -> 
          AbsDomSpc.is_bottom (AbsDomSpc.meet_btcons state.abs_spc c) end

    | NotZero (ws,e) ->
      (* We check that e is never 0 *)
      let be = Papp2 (E.Oeq (E.Op_w ws), e, pcast ws (Pconst (B.of_int 0))) in
      begin match AbsExprSpc.bexpr_to_btcons be state.abs_spc with
        | None -> false
        | Some c -> 
          AbsDomSpc.is_bottom (AbsDomSpc.meet_btcons state.abs_spc c) end

    | Valid _ -> true (* This are checked elsewhere *)

      (* We do not check termination for the speculative semantics *)
    | Termination -> true   

  (* Update abs with the abstract memory range for memory accesses. *)
  let rec mem_safety_apply_spc (abs, violations, s_effect) = function
    | Valid (ws,x,e) as pv ->
      begin match AbsDomSpc.var_points_to abs (mvar_of_var x) with
        | Ptrs pts ->
          if List.length pts = 1 then
            let pt = List.hd pts in
            let x_o = Mtexpr.var (AbsDomSpc.get_env abs) (MvarOffset x) in
            let lin_e = AbsExprSpc.linearize_wexpr abs e in
            let c_ws =
              ((int_of_ws ws) / 8)
              |> Coeff.s_of_int
              |> Mtexpr.cst (AbsDomSpc.get_env abs) in
            let ws_plus_e = Mtexpr.binop Texpr1.Add c_ws lin_e in
            let sexpr = Mtexpr.binop Texpr1.Add x_o ws_plus_e
                        |> sexpr_from_simple_expr in

            ( AbsDomSpc.assign_sexpr abs (MmemRange pt) sexpr,
              violations,
              if List.mem pt s_effect then s_effect else pt :: s_effect)
          else (abs, pv :: violations, s_effect)
        | TopPtr -> (abs, pv :: violations, s_effect) end

    | _ -> (abs, violations, s_effect)


  (*-------------------------------------------------------------------------*)
  let rec check_safety_rec state unsafe = function
    | [] -> unsafe
    | c :: t ->
      let unsafe = 
        if is_safe_std state c
        then unsafe
        else (StdSem,c) :: unsafe 
      in
      let unsafe = 
        if is_safe_spc state c
        then unsafe
        else (SpcSem,c) :: unsafe 
      in
      check_safety_rec state unsafe t 
        
  let rec mem_safety_std_rec a = function
    | [] -> a
    | c :: t ->       
      mem_safety_std_rec (mem_safety_apply_std a c) t

  let rec mem_safety_spc_rec a = function
    | [] -> a
    | c :: t ->       
      mem_safety_spc_rec (mem_safety_apply_spc a c) t

  let add_violations : astate -> violation list -> astate = fun state ls ->
    if ls <> [] then Format.eprintf "%a@." pp_violations ls;
    { state with violations = List.sort_uniq v_compare (ls @ state.violations) }
    
  let rec check_safety state loc conds =
    let vsc = check_safety_rec state [] conds in
    let abs_std, mvsc_std, s_effects =
      mem_safety_std_rec (state.abs_std, [], state.s_effects) conds in
    let abs_spc, mvsc_spc, s_effects =
      mem_safety_spc_rec (state.abs_spc, [], s_effects) conds in
    
    let state = { state with abs_std = abs_std;
                             abs_spc = abs_spc;
                             s_effects = s_effects } in
    
    let mvsc_std = List.map (fun x -> StdSem,x) mvsc_std
    and mvsc_spc = List.map (fun x -> SpcSem,x) mvsc_spc in
    let unsafe = vsc @ mvsc_std @ mvsc_spc
                 |> List.map (fun (x,y) -> (loc,x,y)) in
    add_violations state unsafe

      
  (*-------------------------------------------------------------------------*)
  (* TODO: remove initialization in speculative semantics? 
     if not, check that this is correct *)
  (* Initialize variable or array elements lvalues. *)
  let init_mlv_no_array mlv state = 
    { state with abs_std = AbsExprStd.a_init_mlv_no_array mlv state.abs_std;
                 abs_spc = AbsExprSpc.a_init_mlv_no_array mlv state.abs_spc; }
      

  let offsets_of_mvars l = List.map ty_gvar_of_mvar l
                           |> List.filter (fun x -> x <> None)
                           |> List.map (fun x -> MvarOffset (oget x))

  let rec add_offsets_lv assigns = match assigns with
    | [] -> []
    | (ty, Mvalue (Avar v), (lvty, MLvar (Mvalue (Avar vr)))) :: tail ->
      (ty, Mvalue (Avar v), (lvty, MLvar (Mvalue (Avar vr))))
      :: (ty, MvarOffset v, (lvty, MLvar (MvarOffset vr)))
      :: add_offsets_lv tail
    | u :: tail -> u :: add_offsets_lv tail

  (* Prepare the caller for a function call. Returns the state with the
     arguments es evaluated in f input variables.
     Remark: only possible for the standard semantics, as function calls have 
     no speculative semantics. *)
  let aeval_f_args f es state =
    let f_decl = get_fun_def state.prog f |> oget in

    let f_args = fun_args_no_offset f_decl
    and exp_in_tys = f_decl.f_tyin in

    let assigns = combine3 exp_in_tys f_args es
                  |> List.map (fun (x,y,z) -> (x, MLvar y, z)) in

    let abs_std = List.fold_left (fun abs_std (in_ty, mvar, e) ->
        AbsExprStd.abs_assign abs_std in_ty mvar e ) 
        state.abs_std assigns in

    { state with abs_std = abs_std }

  (* Remark: handles variable initialization. 
     Remark: only possible for the standard semantics, as function calls have 
     no speculative semantics. *)
  let aeval_f_return abs ret_assigns =
    List.fold_left (fun abs (out_ty,rvar,(lv,mlvo)) ->
        match mlvo with
        | MLnone -> abs

        | MLvars mlvs ->
          (* Here, we have no information on which elements are initialized. *)
          AbsDomStd.forget_list abs mlvs

        | MLvar mlv -> match ty_mvar mlv with
          | Bty Bool ->
            let rconstr = BVar (Bvar.make rvar true) in
            AbsDomStd.assign_bexpr abs mlv rconstr
            |> AbsExprStd.a_init_mlv_no_array mlvo

          | Bty _ ->
            let mret = Mtexpr.var (AbsDomStd.get_env abs) rvar in

            let lv_size = wsize_of_ty (ty_lval lv)
            and ret_size = wsize_of_ty out_ty in

            (* Numerical abstraction *)
            let expr = match ty_mvar mlv, ty_mvar rvar with
              | Bty Int, Bty Int -> mret
              | Bty (U _), Bty Int ->
                AbsExprStd.wrap_if_overflow abs mret Unsigned lv_size
              | Bty (U _), Bty (U _) ->
                AbsExprStd.cast_if_overflows abs lv_size ret_size mret
              | _, _ -> assert false in

            let s_expr = sexpr_from_simple_expr expr in
            let abs = AbsDomStd.assign_sexpr abs mlv s_expr in

            (* Points-to abstraction *)
            let ptr_expr = PtVars [rvar] in
            let abs = AbsDomStd.assign_ptr_expr abs mlv ptr_expr in

            (* Offset abstraction *)
            let abs = match ty_gvar_of_mvar rvar with
              | None -> abs
              | Some rv ->
                let lrv = L.mk_loc L._dummy rv in
                AbsExprStd.aeval_offset abs out_ty mlv (Pvar lrv) in

            AbsExprStd.a_init_mlv_no_array mlvo abs

          | Arr _ ->
            let mret = Mtexpr.var (AbsDomStd.get_env abs) rvar in

            let lv_size = wsize_of_ty (ty_lval lv)
            and ret_size = wsize_of_ty out_ty in
            assert (lv_size = ret_size); (* may not be necessary *)

            (* Numerical abstractions only.
               Points-to and offset abstraction are not needed for array and 
               array elements *)
            AbsExprStd.assign_arr_expr abs mlv mret)
      
      abs ret_assigns

  (* Remark: only possible for the standard semantics, as function calls have 
   * no speculative semantics. *)
  let forget_f_vars f state =
    let f_decl = get_fun_def state.prog f |> oget in
    let f_vs = fun_args ~expand_arrays:true f_decl
               @ fun_locals ~expand_arrays:true f_decl in

    (* We remove f variables *)
    { state with abs_std = AbsDomStd.remove_vars state.abs_std f_vs }

  let forget_stack_vars state = match state.cstack with
    | [_] | [] -> state
    | _ :: cf :: _ -> forget_f_vars cf state


  (* Forget the values of all variables with have been modified by side-effect
     during a function call.
     Remark: we only log side effects on memory locations, hence we always
     forget global variables.
     Remark: only possible for the standard semantics, as function calls have 
     no speculative semantics. *)
  let forget_side_effect state s_effects =
    let vs_globs = prog_globals ~expand_arrays:true state.env
                   |> List.filter (function
                       | MmemRange pt -> List.mem pt s_effects
                       | _ -> true) in
    {state with abs_std = AbsDomStd.forget_list state.abs_std vs_globs }

  (* Forget the values of memory locations that have *not* been modified. 
     Remark: only possible for the standard semantics, as function calls have 
     no speculative semantics. *)
  let forget_no_side_effect fstate s_effects =
    let nse_vs = get_mem_range fstate.env
                 |> List.filter (function
                     | MmemRange pt -> not (List.mem pt s_effects)
                     | _ -> true) in
    { fstate with abs_std = AbsDomStd.forget_list fstate.abs_std nse_vs }

  (* Prepare a function call. Returns the state where:
     - The arguments of f have been evaluated.
     - The variables of the caller's caller have been *removed*.
     - s_effects is empty. 
     Remark: only possible for the standard semantics, as function calls have 
     no speculative semantics. *)
  let prepare_call state callsite f es =
    debug (fun () -> Format.eprintf "evaluating arguments ...@.");
    let state = aeval_f_args f es state in

    debug (fun () -> Format.eprintf "forgetting variables ...@.");
    let state = forget_stack_vars state in

    let state = { state with 
                  abs_std = AbsDomStd.new_cnstr_blck state.abs_std callsite;
                  abs_spc = AbsDomSpc.new_cnstr_blck state.abs_spc callsite } in

    { state with cstack = f :: state.cstack;
                 s_effects = [] }


  (* Profiling *)
  let () = Prof.record "prepare_call"
  let prepare_call abs callsite f es =
    let t = Sys.time () in
    let r = prepare_call abs callsite f es in
    let t' = Sys.time () in
    let sf = "prepare_call_" ^ f.fn_name in
    let () = 
      if Prof.is_recorded sf
      then ()
      else Prof.record sf in
    let () = Prof.call "prepare_call" (t' -. t) in
    let () = Prof.call sf (t' -. t) in
    r

  (* Remark: only possible for the standard semantics, as function calls have 
   * no speculative semantics. *)
  let get_ret_assgns abs_std f_decl lvs =
    let f_rets_no_offsets = fun_rets_no_offsets f_decl
    and out_tys = f_decl.f_tyout
    and mlvs = List.map (fun x -> 
        (x, AbsExprStd.mvar_of_lvar abs_std x)) lvs in

    combine3 out_tys f_rets_no_offsets mlvs


  (* Remark: only possible for the standard semantics, as function calls have 
   * no speculative semantics. *)
  let return_call state callsite fstate lvs =
    assert ((not state.spec_analysis) && (not fstate.spec_analysis));
    (* We forget side effects of f in the caller *)
    let state = forget_side_effect state fstate.s_effects in

    (* We pop the top-most block of constraints in the callee *)
    let fabs_std = AbsDomStd.pop_cnstr_blck fstate.abs_std callsite
    and fabs_spc = AbsDomSpc.pop_cnstr_blck fstate.abs_spc callsite in
    let fstate = { fstate with abs_std = fabs_std; abs_spc = fabs_spc; } in

    (* We forget variables untouched by f in the callee *)
    let fstate = forget_no_side_effect fstate fstate.s_effects in
    let fname = List.hd fstate.cstack in

    debug(fun () ->
        Format.eprintf "@[<v 0>side effects of %s: @[<hov 2>%a@]@]@."
          fname.fn_name
          (pp_list pp_mvar) (List.map (fun x -> MmemRange x) fstate.s_effects));

    let state = { abs_std = AbsDomStd.meet state.abs_std fstate.abs_std;
                  abs_spc = state.abs_spc; (* in a standard semantics-only 
                                              analysis, this value does not
                                              matter. *)
                  abs_dead_spc = state.abs_dead_spc; (* idem *)
                  spec_analysis = false;
                  it = fstate.it;
                  env = state.env;
                  prog = state.prog;
                  s_effects = List.unique (state.s_effects @ fstate.s_effects);
                  cstack = state.cstack;
                  violations = List.sort_uniq v_compare
                      (state.violations @ fstate.violations) } in

    debug(fun () -> Format.eprintf "evaluating returned values ...@.");
    (* Finally, we assign the returned values in the corresponding lvalues *)
    let f_decl = get_fun_def fstate.prog fname |> oget in
    let r_assgns = get_ret_assgns state.abs_std f_decl lvs in      
    
    let state = { state with abs_std = aeval_f_return state.abs_std r_assgns } in

    debug(fun () -> 
        Format.eprintf "forgetting %s local variables ...@.@." fname.fn_name);
    (* We forget the variables of f to get a smaller abstract element. *)
    forget_f_vars fname state

  let simpl_obtcons = function
    | Some (BLeaf c) -> Some c
    | _ -> None


  (* -------------------------------------------------------------------- *)
  (* Return flags for the different operations.
     This covers a subset of the x86 flags, as described in the Coq
     semantics (x86_instr_decl.v). *)

  (* FIXME *)
  let sf_of_word _sz _w = None
  (* msb w. *)

  (* FIXME *)
  let pf_of_word _sz _w = None
  (* lsb w. *) 

  let zf_of_word sz w =
    Some (Papp2 (E.Oeq (E.Op_w sz),
                 w,
                 pcast sz (Pconst (B.of_int 0))))

  let rflags_of_aluop sz w _vu _vs = 
    let of_f = None               (* FIXME *)
    and cf   = None               (* FIXME *)
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  let rflags_of_bwop sz w =
    let of_f = Some (Pbool false)
    and cf   = Some (Pbool false)
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  let rflags_of_neg sz w _vs = 
    let of_f = None               (* FIXME, same than for rflags_of_aluop *)
    and cf   = None               (* FIXME, must be (w != 0)*)
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  let rflags_of_mul (ov : bool option) =
    (*  OF; CF; SF; PF; ZF *)
    [Some ov; Some ov; None; None; None]

  let rflags_of_div =
    (*  OF; CF; SF; PF; ZF *)
    [None; None; None; None; None]

  let rflags_of_andn sz w =
    let of_f = Some (Pbool false)
    and cf   = Some (Pbool false)
    and sf   = sf_of_word sz w
    and pf   = None
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  (* Remove the carry flag *)
  let nocf = function
    | [of_f;_;sf;pf;zf] -> [of_f;sf;pf;zf]
    | _ -> assert false

  let opn_dflt n = List.init n (fun _ -> None)

  let opn_bin_gen f_flags ws op es =
    let el,er = as_seq2 es in
    let w = Papp2 (op, el, er) in
    let vu = () in
    let vs = () in
    let rflags = f_flags ws w vu vs in
    rflags @ [Some w]

  let opn_bin_alu = opn_bin_gen rflags_of_aluop

  (* -------------------------------------------------------------------- *)
  (* FIXME: check this *)
  let mk_addcarry ws es =
    let el,er,eb = as_seq3 es in    
    let w_no_carry = Papp2 (E.Oadd (E.Op_w ws), el, er) in
    let w_carry = Papp2 (E.Oadd (E.Op_w ws),
                         w_no_carry,
                         pcast ws (Pconst (B.of_int 1))) in

    let eli = Papp1 (E.Oint_of_word ws, el)    (* (int)el *)
    and eri = Papp1 (E.Oint_of_word ws, er) in (* (int)er *)
    let w_i =
      Papp2 (E.Oadd E.Op_int, eli, eri) in (* (int)el + (int)er *)
    let pow_ws = Pconst (B.pow (B.of_int 2) (int_of_ws ws)) in (* 2^ws *)

    (* cf_no_carry is true <=> 2^ws <= el + er      (addition without modulo) *)
    let cf_no_carry = Papp2 (E.Ole E.Cmp_int, pow_ws, w_i ) in
    (* cf_carry    is true <=> 2^ws <= el + er + 1  (addition without modulo) *)
    let cf_carry = Papp2 (E.Ole E.Cmp_int,
                          pow_ws,
                          Papp2 (E.Oadd E.Op_int,
                                 w_i,
                                 Pconst (B.of_int 1))) in

    match eb with
    | Pbool false ->         (* No carry *)
      [Some cf_no_carry; Some w_no_carry] 

    | Pbool true ->          (* Carry *)
      [Some cf_carry; Some w_carry] 

    | _ ->                   (* General case, potential carry *)
      let _w = Pif (Bty (U ws), eb, w_carry, w_no_carry) in
      let _cf = Pif (Bty Bool, eb, cf_carry, cf_no_carry) in

      (* FIXME: make this optional ?*)
      [None; None]
      (* [Some cf; Some w]  *)

  (* FIXME: check this *)
  let mk_subcarry ws es =
    let el,er,eb = as_seq3 es in    
    let w_no_carry = Papp2 (E.Osub (E.Op_w ws), el, er) in
    let w_carry = Papp2 (E.Osub (E.Op_w ws),
                         w_no_carry,
                         pcast ws (Pconst (B.of_int 1))) in

    let eli = Papp1 (E.Oint_of_word ws, el)    (* (int)el *)
    and eri = Papp1 (E.Oint_of_word ws, er) in (* (int)er *)

    (* cf_no_carry is true <=> el < er *)
    let cf_no_carry = Papp2 (E.Olt E.Cmp_int, eli, eri ) in
    (* cf_carry    is true <=> el < er + 1  (sub without modulo) *)
    let cf_carry = Papp2 (E.Ole E.Cmp_int,
                          eli,
                          Papp2 (E.Oadd E.Op_int, eri, Pconst (B.of_int 1))) in

    match eb with
    | Pbool false ->         (* No carry *)
      [Some cf_no_carry; Some w_no_carry] 

    | Pbool true ->          (* Carry *)
      [Some cf_carry; Some w_carry] 

    | _ ->                   (* General case, potential carry *)
      let _w = Pif (Bty (U ws), eb, w_carry, w_no_carry) in
      let _cf = Pif (Bty Bool, eb, cf_carry, cf_no_carry) in

      (* FIXME: make this optional ?*)
      [None; None]
      (* [Some cf; Some w]  *)

  
  (* -------------------------------------------------------------------- *)
  (* Remark: the assignments must be done in the correct order.
     Bitwise operators are ignored for now (result is soundly set to top).
     See x86_instr_decl.v for a desciption of the operators. *)
  let split_opn n opn es = match opn with
    | E.Oset0 ws -> [None;None;None;None;None;
                     Some (pcast ws (Pconst (B.of_int 0)))]

    | E.Osubcarry ws -> mk_subcarry ws es
      
    | E.Oaddcarry ws -> mk_addcarry ws es
                          
    | E.Ox86 (X86_instr_decl.CMP ws) ->
      (* Input types: ws, ws *)
      let el,er = as_seq2 es in
      let w = Papp2 (E.Osub (E.Op_w ws), el, er) in
      let vu = () in
      let vs = () in
      let rflags = rflags_of_aluop ws w vu vs in
      rflags

    (* add unsigned / signed *)
    | E.Ox86 (X86_instr_decl.ADD ws) ->
      opn_bin_alu ws (E.Oadd (E.Op_w ws)) es

    (* sub unsigned / signed *)
    | E.Ox86 (X86_instr_decl.SUB ws) ->
      opn_bin_alu ws (E.Osub (E.Op_w ws)) es

    (* mul unsigned *)
    | E.Ox86 (X86_instr_decl.MUL ws) ->
      let el,er = as_seq2 es in
      let w = Papp2 (E.Omul (E.Op_w ws), el, er) in
      (* FIXME: overflow bit to have the precise flags *)
      (* let ov = ?? in
       * let rflags = rflags_of_mul ov in *)
      let rflags = [None; None; None; None; None] in
      rflags @ [Some w]

    (* div unsigned *)
    | E.Ox86 (X86_instr_decl.DIV ws) ->
      let el,er = as_seq2 es in
      let w = Papp2 (E.Odiv (E.Cmp_w (Unsigned, ws)), el, er) in
      let rflags = rflags_of_div in
      rflags @ [Some w]

    (* div signed *)
    | E.Ox86 (X86_instr_decl.IDIV ws) ->
      let el,er = as_seq2 es in
      let w = Papp2 (E.Odiv (E.Cmp_w (Signed, ws)), el, er) in
      let rflags = rflags_of_div in
      rflags @ [Some w]

    (* increment *)
    | E.Ox86 (X86_instr_decl.INC ws) ->
      let e = as_seq1 es in
      let w = Papp2 (E.Oadd (E.Op_w ws), e,
                     Papp1(E.Oword_of_int ws, Pconst (B.of_int 1))) in
      let vu = () in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    (* decrement *)
    | E.Ox86 (X86_instr_decl.DEC ws) ->
      let e = as_seq1 es in
      let w = Papp2 (E.Osub (E.Op_w ws), e,
                     Papp1(E.Oword_of_int ws,Pconst (B.of_int 1))) in
      let vu = () in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    (* negation *)
    | E.Ox86 (X86_instr_decl.NEG ws) ->
      let e = as_seq1 es in
      let w = Papp1 (E.Oneg (E.Op_w ws), e) in
      let vs = () in
      let rflags = rflags_of_neg ws w vs in
      rflags @ [Some w]

    (* copy *)
    | E.Ox86 (X86_instr_decl.MOV _) ->
      let e = as_seq1 es in 
      [Some e]

    (* FIXME: adding bit shift with flags *)
    (* 
    | ROR    of wsize    (* rotation / right *)
    | ROL    of wsize    (* rotation / left  *)
    | RCR    of wsize    (* rotation / right with carry *)
    | RCL    of wsize    (* rotation / left  with carry *)
    | SHL    of wsize    (* unsigned / left  *)
    | SHR    of wsize    (* unsigned / right *)
    | SAL    of wsize    (*   signed / left; synonym of SHL *)
    | SAR    of wsize    (*   signed / right *)
    | SHLD   of wsize    (* unsigned (double) / left *)
    | SHRD   of wsize    (* unsigned (double) / right *)
    | MULX    of wsize  (* mul unsigned, doesn't affect arithmetic flags *)
    | ADCX    of wsize  (* add with carry flag, only writes carry flag *)
    | ADOX    of wsize  (* add with overflow flag, only writes overflow flag *)
    *)

    (* conditional copy *)
    | E.Ox86 (X86_instr_decl.CMOVcc sz) ->
      let c,el,er = as_seq3 es in
      let e = Pif (Bty (U sz), c, el, er) in
      [Some e] 

    (* bitwise operators *)
    | E.Ox86 (X86_instr_decl.TEST _)
    | E.Ox86 (X86_instr_decl.AND  _)
    | E.Ox86 (X86_instr_decl.ANDN _)
    | E.Ox86 (X86_instr_decl.OR   _)
    | E.Ox86 (X86_instr_decl.NOT  _)        
    | E.Ox86 (X86_instr_decl.XOR  _)

    (* mul signed with truncation *)
    | E.Ox86 (X86_instr_decl.IMUL _)
    | E.Ox86 (X86_instr_decl.IMULr _)
    | E.Ox86 (X86_instr_decl.IMULri _) 

    | _ -> opn_dflt n


  (* -------------------------------------------------------------------- *)
  type flags_heur = { fh_zf : Mtexpr.t option;
                      fh_cf : Mtexpr.t option;}
  
  (* [v] is the variable receiving the assignment. *)
  let opn_heur apr_env opn v = match opn with 
    (* sub carry *) 
    | E.Osubcarry _ ->
      (* FIXME: improve precision by allowing decrement by something else 
         than 1 here. *)
      Some { fh_zf = None;
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var apr_env v)
                             (Mtexpr.cst apr_env (Coeff.s_of_int 1))); }
        
    (* decrement *) 
    | E.Ox86 (X86_instr_decl.DEC _) ->
      Some { fh_zf = Some (Mtexpr.var apr_env v);
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var apr_env v)
                             (Mtexpr.cst apr_env (Coeff.s_of_int 1))); }

    (* (\* sub with borrow *\)
     * | E.Ox86 (X86_instr_decl.SBB _) *)
    | _ ->
      debug (fun () ->
          Format.eprintf "No heuristic for the return flags of %s@."
            (Printer.pp_opn opn));
      None

  exception Heuristic_failed

  let find_heur bv = function
    | None -> raise Heuristic_failed
    | Some heur ->
      let s = Bvar.var_name bv in
      if String.starts_with s "v_cf"
      then Utils.oget ~exn:Heuristic_failed heur.fh_cf
      else if String.starts_with s "v_zf"
      then Utils.oget ~exn:Heuristic_failed heur.fh_zf
      else raise Heuristic_failed

  (* Heuristic for the (candidate) decreasing quantity to prove while
     loop termination. *)  
  let dec_qnty_heuristic abs loop_body loop_cond =
    let heur_leaf leaf = match Mtcons.get_typ leaf with
      | Lincons0.SUPEQ | Lincons0.SUP -> Mtcons.get_expr leaf

      (* We handle the exit condition "x <> 0" as if it was "x > 0" *)
      | Lincons0.DISEQ -> Mtcons.get_expr leaf

      | _ -> raise Heuristic_failed in

    match loop_cond with
    (* If the exit condition is a constraint (i.e. a leaf boolean term),
       then we try to retrieve the expression inside. *)
    | Some (BLeaf sc) -> heur_leaf sc

    (* For boolean variables, we look whether it is a return flag. If that is
       the case, we look for the instruction that set the flag, and use a
       heuristic depending on the operation. *)
    | Some (BVar bv) ->
      let brev = List.rev loop_body in 
      begin try
          List.find_map (fun ginstr -> match ginstr.i_desc with 
              | Copn(lvs,_,opn,_) ->
                List.find_map_opt (fun lv ->
                    match lv with
                    | Lvar x -> 
                      let x_mv = Mvalue (Avar (L.unloc x)) in
                      if Bvar.make x_mv true = Bvar.positive bv 
                      (* We found the assignment where the flag is set *)
                      then
                        (* Register for which the flags are computed. *)
                        let reg_assgn = match List.last lvs with
                          | Lvar r -> Mvalue (Avar (L.unloc r))
                          | Lnone _ -> raise Heuristic_failed
                          | _ -> assert false in

                        let apr_env = AbsDomStd.get_env abs in
                        let heur = opn_heur apr_env opn reg_assgn in
                        Some (find_heur bv heur)
                      else None
                    | _ -> None) lvs

              | _ -> None                
            ) brev
        with Not_found -> raise Heuristic_failed
      end

    | _ -> raise Heuristic_failed


  (* -------------------------------------------------------------------- *)
  (* Check that there are no memory stores and loads. *)
  let check_memory_access_aux f_decl = 

    (* vs_for: integer variable from for loops, which will be inlined to
       a constant integer value. *)
    let rec nm_i vs_for i = match i.i_desc with
      | Cassgn (lv, _, _, e)    -> nm_lv vs_for lv && nm_e vs_for e
      | Copn (lvs, _, _, es)    -> nm_lvs vs_for lvs && nm_es vs_for es
      | Cif (e, st, st')        -> 
        nm_e vs_for e && nm_stmt vs_for st && nm_stmt vs_for st'
      | Cfor (i, _, st)         -> nm_stmt (i :: vs_for) st
      | Cwhile (_, st1, e, st2) -> 
        nm_e vs_for e && nm_stmt vs_for st1 && nm_stmt vs_for st2
      | Ccall (_, lvs, fn, es)  -> 
        let f' = get_fun_def prog fn |> oget in
        nm_lvs vs_for lvs && nm_es vs_for es && nm_fdecl f'

    and nm_fdecl f = nm_stmt [] f.f_body

    and nm_stmt vs_for stmt = List.for_all (nm_i vs_for) stmt

    and nm_e vs_for = function
      | Pconst _ | Pbool _ | Parr_init _ | Pglobal _ | Pvar _ -> true
      | Pget (_, _, e)     -> know_offset vs_for e && nm_e vs_for e
      | Pload _            -> false
      | Papp1 (_, e)       -> nm_e vs_for e
      | Papp2 (_, e1, e2)  -> nm_es vs_for [e1; e2]
      | PappN (_,es)       -> nm_es vs_for es
      | Pif (_, e, el, er) -> nm_es vs_for [e; el; er]

    and nm_es vs_for es = List.for_all (nm_e vs_for) es

    and nm_lv vs_for = function
      | Lnone _ | Lvar _ -> true
      | Laset (_,_,e) -> know_offset vs_for e
      | Lmem _ -> false

    and nm_lvs vs_for lvs = List.for_all (nm_lv vs_for) lvs 

    and know_offset vs_for = function
      | Pconst _ -> true
      | Pvar v -> List.mem v vs_for
      | Papp1 (E.Oneg Op_int, e) -> know_offset vs_for e

      | Papp2 ((Osub Op_int | Omul Op_int | Oadd Op_int), e1, e2) ->
        know_offset vs_for e1 && know_offset vs_for e2

      | _ -> false
    in

    nm_fdecl f_decl 


  (* Memoisation *)
  let nm_memo = Hf.create 16
  let check_memory_access f_decl =
    try Hf.find nm_memo f_decl.f_name with Not_found ->
      let res = check_memory_access_aux f_decl in
      Hf.add nm_memo f_decl.f_name res;
      res

  
  (* The function must not use memory loads/stores, array accesses must be 
     fixed, and arrays in arguments must be fully initialized
     (i.e. cells must be initialized). *)
  let check_valid_call_top st f_decl = 
    (* Function calls have no speculative semantics  *)
    assert (not st.spec_analysis); 
    let cells_init = 
      List.for_all (fun v -> match mvar_of_var v with
          | Mvalue (Aarray _) as mv -> 
            let vs = u8_blast_var ~blast_arrays:true mv in
            List.for_all (function 
                | Mvalue at -> AbsDomStd.check_init st.abs_std at
                | _ -> assert false (* initialization of other arguments
                                       should already have been checked
                                       by the analyzer. *)
              ) vs
          | _ -> true
        ) f_decl.f_args in

    cells_init && check_memory_access f_decl


  (* -------------------------------------------------------------------- *)
  let num_instr_evaluated = ref 0

  let print_ginstr ~print_spc ginstr abs_vals =
    Format.eprintf "@[<v>@[<v>%a@]@;*** %d Instr: %a %a@;@;@]%!"
      (AbsDom2.print ~print_spc:print_spc) abs_vals
      (let a = !num_instr_evaluated in incr num_instr_evaluated; a)
      L.pp_sloc (fst ginstr.i_loc)
      (Printer.pp_instr ~debug:false) ginstr

  let print_binop ~print_spc fmt (cpt_instr,abs1,abs2,abs3) =
    Format.fprintf fmt "@[<v 2>Of %d:@;%a@]@;\
                        @[<v 2>And %d:@;%a@]@;\
                        @[<v 2>Yield:@;%a@]"
      cpt_instr
      (AbsDom2.print ~print_spc) abs1
      (!num_instr_evaluated - 1)
      (AbsDom2.print ~print_spc) abs2
      (AbsDom2.print ~print_spc) abs3

  let print_if_join ~print_spc cpt_instr ginstr labs rabs abs_r =
    Format.eprintf "@;@[<v 2>If join %a for Instr:@;%a @;@;%a@]@."
      L.pp_sloc (fst ginstr.i_loc)
      (Printer.pp_instr ~debug:false) ginstr
      (print_binop ~print_spc) (cpt_instr,
                             labs,
                             rabs,
                             abs_r)

  let print_while_join ~print_spc cpt_instr abs abs_o abs_r =
    Format.eprintf "@;@[<v 2>While Join:@;%a@]@."
      (print_binop ~print_spc) (cpt_instr,
                             abs,
                             abs_o,
                             abs_r)

  let print_while_widening ~print_spc cpt_instr abs abs' abs_r =
    Format.eprintf "@;@[<v 2>While Widening:@;%a@]@."
      (print_binop ~print_spc) (cpt_instr,
                             abs,
                             abs',
                             abs_r)

  let print_return ~print_spc ginstr fabs fname =
    Format.eprintf "@[<v>@[<v>%a@]Returning %s (called line %a):@;@]%!"
      (AbsDom2.print ~print_spc) fabs
      fname
      L.pp_sloc (fst ginstr.i_loc)

  let abs_vals state = (state.abs_std, state.abs_spc, state.abs_dead_spc)

  let rec aeval_ginstr : ('ty,'info) ginstr -> astate -> astate =
    fun ginstr state ->
      debug (fun () ->
        print_ginstr ~print_spc:state.spec_analysis ginstr (abs_vals state));

      (* We stop if the abstract state is bottom *)
      if AbsDomStd.is_bottom state.abs_std &&
         AbsDomSpc.is_bottom state.abs_spc 
      then state
      else
        (* We check the safety conditions *)
        let conds = safe_instr ginstr in
        let state = check_safety state (InProg (fst ginstr.i_loc)) conds in
        aeval_ginstr_aux ginstr state

  and aeval_ginstr_aux : ('ty,'info) ginstr -> astate -> astate =
    fun ginstr state -> match ginstr.i_desc with 
      | Cassgn (lv,tag,ty1, Pif (ty2, c, el, er))
        when Aparam.pif_movecc_as_if ->
        assert (ty1 = ty2);
        let cl = { ginstr with i_desc = Cassgn (lv, tag, ty1, el) } in
        let cr = { ginstr with i_desc = Cassgn (lv, tag, ty2, er) } in
        aeval_if ~spec:false ginstr c [cl] [cr] state

      | Copn (lvs,tag,E.Ox86 (X86_instr_decl.CMOVcc sz),es)
        when Aparam.pif_movecc_as_if ->
        let c,el,er = as_seq3 es in
        let lv = as_seq1 lvs in
        let cl = { ginstr with i_desc = Cassgn (lv, tag, Bty (U sz), el) } in
        let cr = { ginstr with i_desc = Cassgn (lv, tag, Bty (U sz), er) } in
        aeval_if ~spec:false ginstr c [cl] [cr] state

      | Cassgn (lv, _, _, e) ->
        let abs_std = AbsExprStd.abs_assign
            state.abs_std 
            (ty_lval lv)
            (AbsExprStd.mvar_of_lvar state.abs_std lv) 
            e in
        let abs_spc = AbsExprSpc.abs_assign
            state.abs_spc 
            (ty_lval lv)
            (AbsExprSpc.mvar_of_lvar state.abs_spc lv) 
            e in
        { state with abs_std = abs_std; abs_spc = abs_spc; }

      | Copn(lvs, _, Expr.Ox86 (X86_instr_decl.LFENCE), es) ->
        assert (lvs = [] && es = []);
        (* We update [abs_dead_spc] with the memory accesses of [abs_spc] *)
        let abs_dead_spc2 = spc_to_dead_spc state.abs_spc in
        let abs_dead_spc = AbsDomSpc.join state.abs_dead_spc abs_dead_spc2 in
        
        { state with abs_spc = std_to_spc state.abs_std;
                     abs_dead_spc = abs_dead_spc; };

      | Copn (lvs,_,opn,es) ->
        (* Remark: the assignments must be done in the correct order. *)
        let assgns = split_opn (List.length lvs) opn es in
        let abs_std = AbsExprStd.abs_assign_opn state.abs_std lvs assgns
        and abs_spc = AbsExprSpc.abs_assign_opn state.abs_spc lvs assgns in

        { state with abs_std = abs_std; abs_spc = abs_spc; }

      | Cif(e,c1,c2) ->
        aeval_if ~spec:true ginstr e c1 c2 state

      | Cwhile(_,c1, e, c2) ->
        let prog_pt = fst ginstr.i_loc in

        (* We add a disjunctive constraint block. *)
        let abs_std = AbsDomStd.new_cnstr_blck state.abs_std prog_pt
        and abs_spc = AbsDomSpc.new_cnstr_blck state.abs_spc prog_pt in
        let state = { state with abs_std = abs_std; abs_spc = abs_spc; } in

        let cpt = ref 0 in
        let state = aeval_gstmt c1 state in

        (* We now check that e is safe *)
        let conds = safe_e e in
        let state = check_safety state (InProg prog_pt) conds in

        (* Given an abstract state, compute the loop condition expression. 
           Only useful for the standard semantics. *)
        let oec abs = AbsExprStd.bexpr_to_btcons e abs in

        (* Candidate decreasing quantity *)
        let ni_e =
          try Some (dec_qnty_heuristic 
                      state.abs_std (c2 @ c1) 
                      (oec state.abs_std))
          with Heuristic_failed -> None in
        (* Variable where we store its value before executing the loop body. *)
        let mvar_ni = MNumInv prog_pt in

        (* We check that if the loop does not exit, then ni_e decreased by
             at least one. 
           Only for the standard semantics. *)
        let check_ni_dec state = 
          if AbsDomStd.is_bottom state.abs_std then state
          else
            match ni_e with
            | None -> (* Here, we cannot prove termination *)
              let violation = (InProg prog_pt, StdSem, Termination) in
              add_violations state [violation]

            | Some nie ->
              let env = AbsDomStd.get_env state.abs_std in
              let nie = Mtexpr.extend_environment nie env in

              (* (initial nie) - nie *)
              let e = Mtexpr.(binop Sub (var env mvar_ni) nie) in

              (* We assume the loop does not exit, and check whether the 
                 candidate decreasing quantity indeed decreased. *)
              let state_in = match oec state.abs_std with
                | Some ec -> 
                  { state with 
                    abs_std = AbsDomStd.meet_btcons state.abs_std ec }
                | None -> state in

              debug(fun () -> 
                  Format.eprintf "@[<v 2>Checking the numerical quantity in:@;\
                                  %a@]@."
                    (AbsDom2.print ~print_spc:false) (* only std semantics *)
                    (abs_vals state_in));

              let int = AbsDomStd.bound_texpr state_in.abs_std e
              and zint = AbsDomStd.bound_variable state_in.abs_std mvar_ni
              and test_intz =
                Interval.of_scalar (Scalar.of_int 0) (Scalar.of_infty 1)
              and test_into =
                Interval.of_scalar (Scalar.of_int 1) (Scalar.of_infty 1) in

              debug(fun () ->
                  Format.eprintf "@[<v>@;Numerical quantity decreasing by:@;\
                                  @[%a@]@;\
                                  Initial numerical quantity in interval:@;\
                                  @[%a@]@;@]"
                    Interval.print int
                    Interval.print zint;);

              if (Interval.is_leq int test_into) &&
                 (Interval.is_leq zint test_intz) then state
              else
                let violation = (InProg prog_pt, StdSem, Termination) in
                add_violations state [violation] in


        (* ⟦body⟧state_i ∪ state *)
        let eval_body state_i state =
          let cpt_instr = !num_instr_evaluated - 1 in

          let state_o = aeval_gstmt (c2 @ c1) state_i in

          (* We check that if the loop does not exit, then ni_e decreased by
             at least one *)
          let state_o = check_ni_dec state_o in

          (* We forget the variable storing the initial value of the 
             candidate decreasing quantity.
             The speculative semantics abstraction domain does not 
             include this variable. *)
          let state_o = { state_o with 
                          abs_std = 
                            AbsDomStd.forget_list
                              state_o.abs_std [mvar_ni] } in

          let abs_r_std = AbsDomStd.join state.abs_std state_o.abs_std in
          let abs_r_spc = AbsDomSpc.join state.abs_spc state_o.abs_spc in
          let abs_r_dead_spc =
            AbsDomSpc.join state.abs_dead_spc state_o.abs_dead_spc in
          debug (fun () ->
              print_while_join ~print_spc:state.spec_analysis
                cpt_instr 
                (abs_vals state)
                (abs_vals  state_o) 
                (abs_r_std, abs_r_spc, abs_r_dead_spc));
          { state_o with abs_std = abs_r_std; 
                         abs_spc = abs_r_spc;
                         abs_dead_spc = abs_r_dead_spc; } in

        let enter_loop state =
          debug (fun () -> Format.eprintf "Loop %d@;" !cpt);
          cpt := !cpt + 1;
          let state = match oec state.abs_std with
            | Some ec ->
              debug (fun () -> Format.eprintf "Meet with %a@;" pp_btcons ec);
              { state with abs_std = AbsDomStd.meet_btcons state.abs_std ec }
            | None ->
              debug (fun () -> Format.eprintf "No meet");
              state in

          (* We evaluate a quantity that we try to prove is decreasing. *)
          debug (fun () ->
              Format.eprintf "@[<v>Candidate decreasing numerical quantity:@;\
                              @[%a@]@;@;@]"
                (pp_opt Mtexpr.print) ni_e);

          (* We evaluate the initial value of the candidate decreasing
             quantity. 
             Only for the standard semantics. *)
          match ni_e with
            | None -> state
            | Some nie ->
              { state with 
                abs_std = AbsDomStd.assign_sexpr state.abs_std
                                 mvar_ni
                                 (sexpr_from_simple_expr nie) } in

        (* Unroll one time the loop. *)
        let unroll_once state = eval_body (enter_loop state) state in

        let rec unroll_times i state pre_state =
          if i = 0 then (state,pre_state)
          else unroll_times (i - 1) (unroll_once state) (Some state) in

        let is_stable state pre_state =
          (pre_state <> None) &&
          (AbsDomStd.is_included state.abs_std (oget pre_state).abs_std) &&
          (AbsDomSpc.is_included state.abs_spc (oget pre_state).abs_spc) in

        let exit_loop state =
          debug (fun () -> Format.eprintf "Exit loop@;");
          match obind flip_btcons (oec state.abs_std) with
          | Some neg_ec ->
            { state with abs_std = AbsDomStd.meet_btcons state.abs_std neg_ec }
          | None -> state in

        (* Simple heuristic for the widening threshold.
           Basically, if the loop condition is a return flag, we use the 
           candidate decreasing numerical quantity to make the threshold. *)
        let smpl_thrs abs = match simpl_obtcons (oec abs) with
          | Some _ as constr -> constr
          | None -> omap (fun e -> Mtcons.make e Lincons1.SUP) ni_e in
            
        let rec stabilize state pre_state =
          if is_stable state pre_state then exit_loop state
          else
            let cpt_instr = !num_instr_evaluated - 1 in
            let state' = unroll_once state in
            let w_abs_std =
              AbsDomStd.widening
                (smpl_thrs state.abs_std) (* this is used as a threshold *)
                state.abs_std state'.abs_std in

            (* no threshold from the loop condition for the speculative
               semantics *)
            let w_abs_spc =
              AbsDomSpc.widening None state.abs_spc state'.abs_spc in
            let w_abs_dead_spc =
              AbsDomSpc.widening None state.abs_dead_spc state'.abs_dead_spc in
            debug(fun () ->
                print_while_widening ~print_spc:state.spec_analysis
                  cpt_instr
                  (abs_vals state)
                  (abs_vals state')
                  (w_abs_std,w_abs_spc,w_abs_dead_spc));
            stabilize
              { state' with abs_std = w_abs_std;
                            abs_spc = w_abs_spc;
                            abs_dead_spc = w_abs_dead_spc; }
              (Some state) in

        let rec stabilize_b state_i pre_state =
          let cpt_i = !num_instr_evaluated - 1 in
          let state = eval_body state_i pre_state in

          if is_stable state (Some pre_state) then exit_loop state
          else
            let state_i' = enter_loop state in

            let w_abs_std =
              AbsDomStd.widening
                (smpl_thrs state_i.abs_std) (* this is used as a threshold *)
                state_i.abs_std state_i'.abs_std in

            (* no threshold here from the loop condition for the
               speculative semantics *)
            let w_abs_spc =
              AbsDomSpc.widening None state_i.abs_spc state_i'.abs_spc in
            let w_abs_dead_spc =
              AbsDomSpc.widening None state_i.abs_dead_spc state_i'.abs_dead_spc in
            debug(fun () ->
                print_while_widening ~print_spc:state.spec_analysis
                  cpt_i
                  (abs_vals state_i)
                  (abs_vals state_i')
                  (w_abs_std, w_abs_spc,w_abs_dead_spc));
            stabilize_b
              { state_i' with abs_std = w_abs_std; 
                              abs_spc = w_abs_spc;
                              abs_dead_spc = w_abs_dead_spc; }
              state in

        (* We first unroll the loop k_unroll times. 
           (k_unroll is a parameter of the analysis) *)
        let state, pre_state = unroll_times Aparam.k_unroll state None in

        (* We stabilize the abstraction (in finite time) using widening. *)
        let state =
          if Aparam.widening_out then stabilize state pre_state
          else stabilize_b (enter_loop state) state in

        (* We pop the disjunctive constraint block *)
        let abs_std = AbsDomStd.pop_cnstr_blck state.abs_std prog_pt
        and abs_spc = AbsDomSpc.pop_cnstr_blck state.abs_spc prog_pt in
        { state with abs_std = abs_std; abs_spc = abs_spc; } 


      | Ccall(_, lvs, f, es) ->
        assert (not state.spec_analysis);
        let f_decl = get_fun_def state.prog f |> oget in
        let fn = f_decl.f_name in

        debug (fun () -> Format.eprintf "@[<v>Call %s:@;@]%!" fn.fn_name);
        let callsite,_ = ginstr.i_loc in

        let state_i = prepare_call state callsite f es in

        let fstate = aeval_call f f_decl callsite state_i in

        (* We check the safety conditions of the return *)
        let conds = safe_return f_decl in
        let fstate = check_safety fstate (InReturn fn) conds in

        debug(fun () ->
            print_return ~print_spc:state.spec_analysis
              ginstr (abs_vals fstate) fn.fn_name);

        return_call state callsite fstate lvs

      | Cfor(i, (d,e1,e2), c) ->
        let prog_pt = fst ginstr.i_loc in

        let check_spec_bounds z1 z2 =
          if state.spec_analysis then 
            match AbsExprSpc.aeval_cst_int state.abs_spc e1, 
                  AbsExprSpc.aeval_cst_int state.abs_spc e2 with
            | Some z1', Some z2' ->
              if z1' = z1 && z2' = z2
              then () 
              else begin
                Format.eprintf "@[<v>Error: for loop bounds for the standard \
                                and speculative semantics are different:@;\
                                std:%d and spec:%d@;std:%d and spec:%d@]"
                  z1 z1 z2 z2';
                assert false
              end
            | _ ->
              Format.eprintf "@[<v>For loop (speculative semantics): \
                              I was expecting a constant integer expression.@;\
                              Expr1:@[%a@]@;Expr2:@[%a@]@;@."
                (Printer.pp_expr ~debug:true) e1
                (Printer.pp_expr ~debug:true) e2;
              assert false in


        match AbsExprStd.aeval_cst_int state.abs_std e1, 
              AbsExprStd.aeval_cst_int state.abs_std e2 with
        | Some z1, Some z2 ->
          check_spec_bounds z1 z2;
          if z1 = z2 then state else
            let init_i, final_i, op = match d with
              | UpTo -> assert (z1 < z2); (z1, z2 - 1, fun x -> x + 1)
              | DownTo -> assert (z1 < z2); (z2, z1 + 1, fun x -> x - 1) in

            let rec mk_range i f op =
              if i = f then [i] else i :: mk_range (op i) f op in

            let range = mk_range init_i final_i op
            and mvari = Mvalue (Avar (L.unloc i)) in
            let apr_env_std = AbsDomStd.get_env state.abs_std 
            and apr_env_spc = AbsDomSpc.get_env state.abs_spc in 

            List.fold_left ( fun state ci ->
                (* We add a disjunctive constraint block. *)
                let std = AbsDomStd.new_cnstr_blck state.abs_std prog_pt
                and spc = AbsDomSpc.new_cnstr_blck state.abs_spc prog_pt in
                let state = { state with abs_std = std; abs_spc = spc; } in

                (* We set the integer variable i to ci. *)
                let expr_ci_std = Mtexpr.cst apr_env_std (Coeff.s_of_int ci)
                                  |> sexpr_from_simple_expr in
                let abs_std = 
                  AbsDomStd.assign_sexpr state.abs_std mvari expr_ci_std in

                let expr_ci_spc = Mtexpr.cst apr_env_spc (Coeff.s_of_int ci)
                                  |> sexpr_from_simple_expr in
                let abs_spc = 
                  AbsDomSpc.assign_sexpr state.abs_spc mvari expr_ci_spc in

                (* TODO: should we keep initialization for speculative 
                   semantics ?*)
                let state =
                  { state with
                    abs_std = AbsDomStd.is_init abs_std (Avar (L.unloc i));
                    abs_spc = AbsDomSpc.is_init abs_spc (Avar (L.unloc i)); }
                  |> aeval_gstmt c in

                (* We pop the disjunctive constraint block. *)
                let abs_std = AbsDomStd.pop_cnstr_blck state.abs_std prog_pt
                and abs_spc = AbsDomSpc.pop_cnstr_blck state.abs_spc prog_pt in
                { state with abs_std = abs_std; abs_spc = abs_spc; } 
              ) state range

        | _ ->
          Format.eprintf "@[<v>For loop: \
                          I was expecting a constant integer expression.@;\
                          Expr1:@[%a@]@;Expr2:@[%a@]@;@."
            (Printer.pp_expr ~debug:true) e1
            (Printer.pp_expr ~debug:true) e2;
          assert false

  and aeval_call : funname -> unit func -> L.t -> astate -> astate =
    fun f f_decl callsite st_in ->
    assert (not st_in.spec_analysis);
    let itk = ItFunIn (f,callsite) in

    match aeval_call_strategy callsite f_decl st_in with 
    | Call_Direct -> aeval_body f_decl.f_body st_in

    (* Precond: [check_valid_call_top st_in] must hold:
       the function must not use memory loads/stores, array accesses must be 
       fixed, and arrays in arguments must be fully initialized
       (i.e. cells must be initialized). *)
    | Call_TopByCallSite ->
      (* f has been abstractly evaluated at this callsite before *)
      if ItMap.mem itk st_in.it then 
        let fabs = ItMap.find itk st_in.it in
        match FAbs.apply st_in.abs_std fabs with
        | Some (f_abs_out, f_effects) ->
          { st_in with abs_std = f_abs_out;
                       s_effects = f_effects; } 

        | None -> assert false    (* that should not be possible *)

      (* We abstractly evaluate f for the first time *)
      else
        (* Set the abstract state to top (and remove all disjunction).
             Moreover, all arguments of [f_decl] are assumed
             initialized (including array cells). *)
        let st_in_ndisj = 
          let mvars = List.map mvar_of_var f_decl.f_args
                      |> u8_blast_vars ~blast_arrays:true in
          let abs = AbsDomStd.top_ni st_in.abs_std in
          let abs = List.fold_left (fun abs mv -> match mv with
              | Mvalue at -> AbsDomStd.is_init abs at
              | _ -> assert false
            ) abs mvars in
          
          { st_in with abs_std = abs } 
        in

        let st_out_ndisj = aeval_body f_decl.f_body st_in_ndisj in

        (* We make a new function abstraction for f. Roughly, it is of the form:
           input |--> (output,effects) *)
        let fabs = FAbs.make 
            st_in_ndisj.abs_std
            st_out_ndisj.abs_std
            st_out_ndisj.s_effects in

        let st_out_ndisj = { st_out_ndisj with
                             it = ItMap.add itk fabs st_out_ndisj.it } in

        (* It remains to add the disjunctions of the call_site to st_out *)
        { st_out_ndisj with 
          abs_std = AbsDomStd.to_shape st_out_ndisj.abs_std st_in.abs_std }
        
  and aeval_if ~spec ginstr e c1 c2 state =
    (* Standard semantics. *)
    let eval_cond_std state = function
      | Some ec -> AbsDomStd.meet_btcons state.abs_std ec
      | None -> state.abs_std in
    let oec_std = AbsExprStd.bexpr_to_btcons e state.abs_std in

    let labs_std, rabs_std =
      if Aparam.if_disj && is_some (simpl_obtcons oec_std) then
        let ec = simpl_obtcons oec_std |> oget in
        AbsDomStd.add_cnstr state.abs_std ~meet:true ec (fst ginstr.i_loc)
      else
        (* FIXME: check that the fact that we do not introduce a 
           disjunction node does not create issues. *)
        let noec_std = obind flip_btcons oec_std in
        ( eval_cond_std state oec_std, eval_cond_std state noec_std ) in

    (* Speculative semantics. *)
    let eval_cond_spc state = function
      | Some ec -> AbsDomSpc.meet_btcons state.abs_spc ec
      | None -> state.abs_spc in
    let oec_spc = AbsExprSpc.bexpr_to_btcons e state.abs_spc in

    let labs_spc, rabs_spc =
      let meet = not spec in
      if Aparam.if_disj && is_some (simpl_obtcons oec_spc) then
        let ec = simpl_obtcons oec_spc |> oget in
        AbsDomSpc.add_cnstr state.abs_spc ~meet:meet ec (fst ginstr.i_loc)
      else
        (* FIXME: idem, see fixme above. *)
        let noec_spc = obind flip_btcons oec_spc in
        ( eval_cond_spc state oec_spc, eval_cond_spc state noec_spc ) in

    (* Branches evaluation *)
    let lstate =
      aeval_gstmt c1 { state with abs_std = labs_std;
                                  abs_spc = labs_spc; } in

    let cpt_instr = !num_instr_evaluated - 1 in

    (* We abstractly evaluate the right branch
       Be careful the start from lstate, as we need to use the
       updated abstract iterator. *)
    let rstate =
      aeval_gstmt c2 { lstate with abs_std = rabs_std;
                                   abs_spc = rabs_spc;
                                   abs_dead_spc = state.abs_dead_spc; } in

    let abs_res_std = AbsDomStd.join lstate.abs_std rstate.abs_std 
    and abs_res_spc = AbsDomSpc.join lstate.abs_spc rstate.abs_spc 
    and abs_res_dead_spc =
      AbsDomSpc.join lstate.abs_dead_spc rstate.abs_dead_spc in
    debug (fun () ->
        print_if_join ~print_spc:state.spec_analysis 
          cpt_instr ginstr 
          (abs_vals lstate) 
          (abs_vals rstate)
          (abs_res_std, abs_res_spc, abs_res_dead_spc));
    { rstate with abs_std     = abs_res_std;
                  abs_spc     = abs_res_spc;
                  abs_dead_spc = abs_res_dead_spc; }

  and aeval_body f_body state =
    debug (fun () -> Format.eprintf "Evaluating the body ...@.@.");
    aeval_gstmt f_body state

  and aeval_gstmt : ('ty,'i) gstmt -> astate -> astate =
    fun gstmt state ->
    let state = List.fold_left (fun state ginstr ->
        aeval_ginstr ginstr state)
        state gstmt in
    let () = debug (fun () ->
        if gstmt <> [] then
          Format.eprintf "%a%!"
            (AbsDom2.print ~print_spc:state.spec_analysis) 
            (abs_vals state)) in
    state

  (* Select the call strategy for [f_decl] in [st_in] *)
  and aeval_call_strategy callsite f_decl st_in =
    let strat = match Aparam.abs_call_strategy with
    | CallDirectAll -> Call_Direct
    (* | CallWideningAll -> Call_WideningByCallSite *)
    | CallTopHeuristic ->
      if check_valid_call_top st_in f_decl
      then Call_TopByCallSite 
      else Call_Direct in

    debug(fun () -> Format.eprintf "Call strategy for %s at %a: %a@." 
             f_decl.f_name.fn_name
             L.pp_sloc callsite
             pp_call_strategy strat);
    strat
  
  (*------------------------------------------------------------------------*)
  let print_mem_ranges state =
    debug(fun () -> Format.eprintf
             "@[<v 0>@;Final offsets full abstract value:@;@[%a@]@]@."
             (AbsDom2.print ~print_spc:state.spec_analysis) 
             (abs_vals state))

  let print_var_interval_std state fmt mvar =
    let int_std = AbsDomStd.bound_variable state.abs_std mvar in
    Format.fprintf fmt "@[%a: %a@]"
      pp_mvar mvar
      Interval.print int_std

  let print_var_interval_spc state fmt mvar =
    let int_spc = AbsDomSpc.bound_variable state.abs_spc mvar in
    Format.fprintf fmt "@[%a: %a@]"
      pp_mvar mvar
      Interval.print int_spc

  let mem_ranges_printer state f_decl fmt () =
    let in_vars = fun_in_args_no_offset f_decl
                  |> List.map otolist
                  |> List.flatten in
    let vars_to_keep = in_vars @ get_mem_range state.env in
    let vars = in_vars @ fun_vars ~expand_arrays:false f_decl state.env in
    let rem_vars = List.fold_left (fun acc v ->
        if (List.mem v vars_to_keep) then acc else v :: acc )
        [] vars in

    let abs_proj_std = 
      AbsDomStd.pop_cnstr_blck
        (AbsDomStd.forget_list state.abs_std rem_vars) 
        L._dummy                (* We use L._dummy for the initial block *)
    in
    let abs_proj_spc = 
      AbsDomSpc.pop_cnstr_blck
        (AbsDomSpc.forget_list state.abs_spc rem_vars) 
        L._dummy                (* We use L._dummy for the initial block *)
    in
    let abs_proj_dead_spc = AbsDomSpc.forget_list state.abs_dead_spc rem_vars in

    let sb = !only_rel_print in (* Not very clean *)
    only_rel_print := true;
    Format.fprintf fmt "@[%a@]"
      (AbsDom2.print ~print_spc:state.spec_analysis)
      (abs_proj_std, abs_proj_spc, abs_proj_dead_spc);
    only_rel_print := sb


  let analyze () =
    (* Stats *)
    let exception UserInterupt in

    let t_start = Sys.time () in
    let print_stats _ =
      Format.eprintf "@[<v 0>Duration: %1f@;%a@]"
        (Sys.time () -. t_start)
        Prof.print () in

    try
      (* We print stats before exciting *)
      let hndl = Sys.Signal_handle (fun _ -> print_stats (); raise UserInterupt) in
      let old_handler = Sys.signal Sys.sigint hndl in

      let state = init_state main_decl prog in

      (* We abstractly evaluate the main function *)
      let final_st = aeval_gstmt main_decl.f_body state in

      (* We check the safety conditions of the return *)
      let conds = safe_return main_decl in
      let final_st = check_safety final_st (InReturn main_decl.f_name) conds in

      debug(fun () -> Format.eprintf "%a" pp_violations final_st.violations);
      print_mem_ranges final_st;

      let () = debug (fun () -> print_stats ()) in
      let () = Sys.set_signal Sys.sigint old_handler in

      ( final_st.violations,
        mem_ranges_printer final_st main_decl,
        print_var_interval_std final_st,
        print_var_interval_spc final_st )
    with
    | Manager.Error _ as e -> hndl_apr_exc e
end


module type ExportWrap = sig
  val main : unit Prog.func
  val prog : unit Prog.prog
end

module AbsAnalyzer (EW : ExportWrap) = struct
  
  module EW = struct
      (* We ensure that all variable names are unique *)
    let main,prog = MkUniq.mk_uniq EW.main EW.prog
  end

  let parse_pt_rel s = match String.split_on_char ';' s with
    | [pts;rels] ->
      let relationals =
        if rels = ""
        then Some []
        else String.split_on_char ',' rels |> some in
      let pointers =
        if pts = ""
        then Some []
        else String.split_on_char ',' pts |> some in
      { relationals = relationals;
        pointers = pointers; }
      
    | [_] ->
      raise (Failure "-safetyparam ill-formed (maybe you forgot a ';' ?)")
    | _ ->
      raise (Failure "-safetyparam ill-formed (too many ';' ?)")

  let parse_pt_rels s = String.split_on_char ':' s |> List.map parse_pt_rel

  let parse_params : string -> (string option * analyzer_param list) list =
    fun s ->
      String.split_on_char '|' s
      |> List.map (fun s -> match String.split_on_char '>' s with
          | [fn;ps] -> (Some fn, parse_pt_rels ps)
          | [ps] -> (None, parse_pt_rels ps)
          | _ -> raise (Failure "-safetyparam ill-formed (too many '>' ?)"))

  let analyze () =
    try
    let ps_assoc = omap_dfl (fun s_p -> parse_params s_p)
        [ None, [ { relationals = None; pointers = None } ]]
        !Glob_options.safety_param in

    let ps = try List.assoc (Some EW.main.f_name.fn_name) ps_assoc with
      | Not_found -> try List.assoc None ps_assoc with
        | Not_found -> [ { relationals = None; pointers = None } ] in

    let pt_vars =
      List.fold_left (fun acc p -> match p.pointers with
          | None -> acc
          | Some l -> l @ acc) [] ps
      |> List.sort_uniq Stdlib.compare
      |> List.map (fun pt ->
          try List.find (fun x -> x.v_name = pt) EW.main.f_args with
          | Not_found ->
            raise (Failure ("-safetyparam ill-formed (" ^ pt ^ " unknown)"))) in

    let npt = List.filter (fun x -> not (List.mem x pt_vars)) EW.main.f_args
              |> List.map (fun x -> MmemRange (MemLoc x)) in

    let l_res = List.map (fun p ->
        let module AbsInt = AbsInterpreter (struct
            include EW
            let param = p
          end) in
        AbsInt.analyze ()) ps in

    match l_res with
    | [] -> raise (Failure "-safetyparam ill-formed (empty list of params)")
    | (violations, _, print_mvar_interval_std, print_mvar_interval_spc) :: _->
      let pp_mem_range fmt = match npt with
        | [] -> Format.fprintf fmt ""
        | _ ->
      Format.eprintf "@[<v 2>Memory ranges (standard semantics):@;%a@]@;\
                      @[<v 2>Memory ranges (speculative semantics):@;%a@]@;"
        (pp_list print_mvar_interval_std) npt
        (pp_list print_mvar_interval_spc) npt in
      
      Format.eprintf "@.@[<v>%a@;\
                      %t\
                      %a@]@."
        pp_violations violations
        pp_mem_range
        (pp_list (fun fmt (_,f,_,_) -> f fmt ())) l_res;

      if violations <> [] then begin
        Format.eprintf "@[<v>Program is not safe!@;@]@.";
        exit(2)
      end;
    with | Manager.Error _ as e -> hndl_apr_exc e
end
