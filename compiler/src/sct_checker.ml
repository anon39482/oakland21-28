open Prog 

let mem = V.mk "memory" Reg tbool L._dummy

type sct_model =
  | V1 
  | V4
  | V4_weak

module V1 = struct

  let rec sct_e ~needed s e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ -> s
    | Pglobal _ -> (* will be translated into a load *)
      s
      
    | Pvar x -> 
      let x = L.unloc x in
      if needed then Sv.add x s else s 
      
    | Pget(_, x, e) -> 
      let x = L.unloc x in
      assert (is_stack_var x);
      let s = if needed then Sv.add x s else s in
      sct_e ~needed:true s e
      
    | Pload(_, x, e) ->
      let x = L.unloc x in
      assert (not(is_stack_var x));
      let s = if needed then Sv.add mem s else s in
      sct_e ~needed:true (Sv.add x s) e 
 
    | Papp1 (_, e) -> sct_e ~needed s e
    | Papp2 (_, e1, e2) -> sct_es ~needed s [e1;e2]
    | PappN (_, es) -> sct_es ~needed s es 
    | Pif(_,e1,e2,e3) -> sct_es ~needed s [e1;e2;e3]

  and sct_es ~needed s es = 
    List.fold_left (sct_e ~needed) s es 

  let sct_lv sO lv = 
    match lv with
    | Lnone _ -> Sv.empty, Sv.empty, false
    | Lvar x  -> 
      let x = L.unloc x in
      let needed = Sv.mem x sO in
      Sv.empty, Sv.singleton x, needed 
        
    | Lmem(_,x,e) -> 
      let x = L.unloc x in
      assert (not (is_stack_var x));
      let needed = Sv.mem mem sO in
      sct_e ~needed:true (Sv.singleton x) e, Sv.empty, needed
  
    | Laset(_,x,e) ->
      let x = L.unloc x in
      assert (is_stack_var x);
      let needed = Sv.mem x sO in
      sct_e ~needed:true Sv.empty e, Sv.empty, needed
  
  let sct_lvs sO lvs =
    let l = List.map (sct_lv sO) lvs in
    let needed = List.exists (fun (_,_,needed) -> needed) l in
    let to_remove = 
      List.fold_left 
        (fun to_remove (_, s, _) -> Sv.union to_remove s) Sv.empty l in
    let to_add = 
      List.fold_left 
        (fun to_add (s, _, _) -> Sv.union to_add s) Sv.empty l in
    to_add, to_remove, needed
  
  
  let pp_x msg s =
    Format.eprintf  "%s = {@[%a@]}@." msg
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements s) 
  
  let pp_X fmt iC = 
      Format.fprintf fmt "@[<h> C = { %a }@]@ "
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements iC) 
  
  let rec sct_i i oC = 
  
    let x, i_desc = 
      match i.i_desc with
      | Cassgn(x,_,_,e) ->
        let doit sO = 
          let to_add, to_remove, needed = sct_lv sO x in
          let x = (Sv.union to_add (Sv.diff sO to_remove)) in
          let xe = sct_e ~needed  Sv.empty e in
          Sv.union x xe in
  
        doit oC, i.i_desc
      
      | Copn(_, _, Expr.Ox86 (X86_instr_decl.LFENCE), _) ->
        oC, i.i_desc
      
      | Copn(xs, _, _, es) ->
        let doit sO = 
          let to_add, to_remove, needed = sct_lvs sO xs in
          let x = (Sv.union to_add (Sv.diff sO to_remove)) in
          let xe = sct_es ~needed  Sv.empty es in
          Sv.union x xe in    
        doit oC, i.i_desc
      
      | Cif (e,c1,c2) ->
        let (iC1, c1) = sct_c c1 oC in
        let (iC2, c2) = sct_c c2 oC in
        let needed = true in
        let iC = sct_e ~needed (Sv.union iC1 iC2) e in
        iC, Cif(e,c1,c2)
   
  
                
      | Cwhile(a,c1,e,c2) -> 
        (* c1;while e {c2; c1} *)
        let rec aux oC = 
          let iC1, c1 = sct_c c1 oC in
          let iC2, c2 = sct_c c2 iC1 in
          let needed = true in
          let iC = sct_e ~needed iC2 e in
          if Sv.subset iC oC then
            iC1, c1, c2
          else
            aux (Sv.union iC oC) in
        let xI, c1, c2 = aux oC in
        xI, Cwhile(a,c1,e,c2)
  
      | Cfor _ -> assert false
  
      | Ccall _ -> assert false in
  
    x, {i_desc; i_loc = i.i_loc; i_info = x }
  
  and sct_c c o = 
    match c with
    | [] -> o, []
    | i :: c ->
      let xc,c = sct_c c o in
      let xi, i = sct_i i xc in
      xi, i::c
  
  
  let rec map_info_i i = 
    let i_desc = 
      match i.i_desc with
      | Cassgn(x,t,ty,e)   -> Cassgn(x,t,ty,e)
      | Copn(xs,t,o,e)     -> Copn(xs,t,o,e) 
      | Cif(e,c1,c2)       -> Cif(e, map_info_c c1, map_info_c c2)
      | Cwhile (a,c1,e,c2) -> Cwhile(a, map_info_c c1, e, map_info_c c2)
      | Cfor _             -> assert false
      | Ccall _            -> assert false in
    {i_desc; i_loc = i.i_loc; i_info = Sv.empty }
  
  and map_info_c c = 
    List.map map_info_i c
  
  let check_fun f = 
    let body = map_info_c f.f_body in
    let iC, _body = sct_c body Sv.empty in
    let to_keep = 
      Sv.add mem (Sv.of_list f.f_args) in
    let iC = 
      Sv.inter to_keep iC in
  
    Format.eprintf "For function %s@." f.f_name.fn_name;
   
    Format.eprintf "%a@.@."
      (Printer.pp_istmt ~debug:false pp_X) _body;
  
    if Sv.mem mem iC then
      Format.eprintf "ERROR: the function %s is not constant time (memory)@."
        f.f_name.fn_name;
  
    Format.eprintf "@.@."

end 

let xs = V.mk "xs" Reg tbool L._dummy

module V4 = struct

  let rec sct_e ~spec ~needed s e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ -> s
    | Pglobal _ -> (* will be translated into a load *)
      if spec && needed then Sv.add xs s else s
      
    | Pvar x -> 
      let x = L.unloc x in
      let s = if needed then Sv.add x s else s in
      if spec && needed && is_stack_var x then Sv.add xs s else s
      
    | Pget(_, x, e) -> 
      let x = L.unloc x in
      assert (is_stack_var x);
      let s = if needed then Sv.add x s else s in
      let s = if spec && needed then Sv.add xs s else s in
      sct_e ~spec ~needed:true s e
      
    | Pload(_, x, e) ->
      let x = L.unloc x in
      assert (not(is_stack_var x));
      let s = if needed then Sv.add mem s else s in
      let s = if spec && needed then Sv.add xs s else s in
      sct_e ~spec ~needed:true (Sv.add x s) e 
 
    | Papp1 (_, e) -> sct_e ~spec ~needed s e
    | Papp2 (_, e1, e2) -> sct_es ~spec ~needed s [e1;e2]
    | PappN (_, es) -> sct_es ~spec ~needed s es 
    | Pif(_,e1,e2,e3) -> sct_es ~spec ~needed s [e1;e2;e3]

  and sct_es ~spec ~needed s es = 
    List.fold_left (sct_e ~spec ~needed) s es 

  let sct_lv ~spec sO lv = 
    match lv with
    | Lnone _ -> Sv.empty, Sv.empty, false
    | Lvar x  -> 
      let x = L.unloc x in
      let needed = 
        if is_stack_var x then
          Sv.mem x sO || Sv.mem xs sO
        else Sv.mem x sO in
      Sv.empty, Sv.singleton x, needed 
        
    | Lmem(_,x,e) -> 
      let x = L.unloc x in
      assert (not (is_stack_var x));
      let needed = Sv.mem mem sO || Sv.mem xs sO in
      sct_e ~spec ~needed:true (Sv.singleton x) e, Sv.empty, needed
  
    | Laset(_,x,e) ->
      let x = L.unloc x in
      assert (is_stack_var x);
      let needed = Sv.mem x sO || Sv.mem xs sO in
      sct_e ~spec ~needed:true Sv.empty e, Sv.empty, needed
  
  let sct_lvs ~spec sO lvs =
    let l = List.map (sct_lv ~spec sO) lvs in
    let needed = List.exists (fun (_,_,needed) -> needed) l in
    let to_remove = 
      List.fold_left 
        (fun to_remove (_, s, _) -> Sv.union to_remove s) Sv.empty l in
    let to_add = 
      List.fold_left 
        (fun to_add (s, _, _) -> Sv.union to_add s) Sv.empty l in
    to_add, to_remove, needed
  
  
  let pp_x msg s =
    Format.eprintf  "%s = {@[%a@]}@." msg
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements s) 
  
  let pp_X fmt (iS, iC) = 
      Format.fprintf fmt "@[<h>S = { %a }        | C = { %a }@]@ "
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements iS) 
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements iC) 
  
  let rec sct_i i (oS, oC) = 
   (* Format.eprintf "@[<h>sct_i %a    %a@]@." 
      (Printer.pp_stmt ~debug:false) [i]
      pp_X (oS, oC); *)
  
    let x, i_desc = 
      match i.i_desc with
      | Cassgn(x,_,_,e) ->
        let doit spec sO = 
          let to_add, to_remove, needed = sct_lv ~spec sO x in
          let x = (Sv.union to_add (Sv.diff sO to_remove)) in
          let xe = sct_e ~spec ~needed  Sv.empty e in
       (*   pp_x "x" x;
          pp_x "xe" xe; *)
          Sv.union x xe in
  
        (doit true oS, doit false oC), i.i_desc
      
      | Copn(_, _, Expr.Ox86 (X86_instr_decl.LFENCE), _) ->
        (Sv.empty, Sv.remove xs (Sv.union oS oC)), i.i_desc
      
      | Copn(xs, _, _, es) ->
        let doit spec sO = 
          let to_add, to_remove, needed = sct_lvs ~spec sO xs in
          let x = (Sv.union to_add (Sv.diff sO to_remove)) in
          let xe = sct_es ~spec ~needed  Sv.empty es in
  (*        Format.eprintf "%s@." (if spec then "Spec" else "CT");
          Format.eprintf "needed = %b@." needed;
          pp_x "x" x;
          pp_x "xe" xe; *)
          Sv.union x xe in    
        (doit true oS, doit false oC), i.i_desc
      
      | Cif (e,c1,c2) ->
        let ((iS1, iC1), c1) = sct_c c1 (oS, oC) in
        let ((iS2, iC2), c2) = sct_c c2 (oS, oC) in
        let needed = true in
        let iS = sct_e ~spec:true ~needed (Sv.union iS1 iS2) e in
        let iC = sct_e ~spec:false ~needed (Sv.union iC1 iC2) e in
        (iS, iC), Cif(e,c1,c2)
   
  
                
      | Cwhile(a,c1,e,c2) -> 
        (* c1;while e {c2; c1} *)
        let rec aux oS oC = 
          let (iS1,iC1), c1 = sct_c c1 (oS,oC) in
          let (iS2,iC2), c2 = sct_c c2 (iS1,iC1) in
          let needed = true in
          let iS = sct_e ~spec:true ~needed iS2 e in
          let iC = sct_e ~spec:false ~needed iC2 e in
          if Sv.subset iS oS && Sv.subset iC oC then
            (iS1,iC1), (* (oS,Oc), *) c1, c2
          else
            aux (Sv.union iS oS) (Sv.union iC oC) in
        let xI, c1, c2 = aux oS oC in
        xI, Cwhile(a,c1,e,c2)
  
      | Cfor _ -> assert false
  
      | Ccall _ -> assert false in
  
    x, {i_desc; i_loc = i.i_loc; i_info = x }
  
  and sct_c c o = 
    match c with
    | [] -> o, []
    | i :: c ->
      let xc,c = sct_c c o in
      let xi, i = sct_i i xc in
      xi, i::c
  
  
  let rec map_info_i i = 
    let i_desc = 
      match i.i_desc with
      | Cassgn(x,t,ty,e)   -> Cassgn(x,t,ty,e)
      | Copn(xs,t,o,e)     -> Copn(xs,t,o,e) 
      | Cif(e,c1,c2)       -> Cif(e, map_info_c c1, map_info_c c2)
      | Cwhile (a,c1,e,c2) -> Cwhile(a, map_info_c c1, e, map_info_c c2)
      | Cfor _             -> assert false
      | Ccall _            -> assert false in
    {i_desc; i_loc = i.i_loc; i_info = Sv.empty, Sv.empty }
  
  and map_info_c c = 
    List.map map_info_i c
  
  let check_fun f = 
    let body = map_info_c f.f_body in
    let (iS, iC), _body = sct_c body (Sv.singleton xs, Sv.empty) in
    let to_keep = 
      Sv.add mem (Sv.add xs (Sv.of_list f.f_args)) in
    let iS, iC = 
      Sv.inter to_keep iS, Sv.inter to_keep iC in
  
    Format.eprintf "For function %s@." f.f_name.fn_name;
   
    Format.eprintf "%a@.@."
      (Printer.pp_istmt ~debug:false pp_X) _body;
  
    if Sv.mem mem iC || Sv.mem mem iS then
      Format.eprintf "ERROR: the function %s is not constant time (memory)@."
        f.f_name.fn_name;
  
    if Sv.mem xs iS then
      Format.eprintf "WARNING: speculative leakages of %s depend of xs@."
        f.f_name.fn_name;
    Format.eprintf "@.@."

end

module V4_weak = struct

  (* For each stack variable [x] we add a variable [#x] representing
     all values that are stored in this variable.
     For all other memory location we over approximate using a common 
     variable xs *)

  type env = var Hv.t 

  let empty_env () = Hv.create 107 

  let get_xs env x = 
    try Hv.find env x
    with Not_found ->
      let name = "#"^x.v_name in
      let xs = V.mk name x.v_kind x.v_ty x.v_dloc in
      Hv.add env x xs;
      xs

  let rec sct_e env ~spec ~needed s e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ -> s
    | Pglobal _ -> s (* since globals are never write and they address are disjoint every where no miss speculation is possible here *) 
      
    | Pvar x -> 
      let x = L.unloc x in
      let s = if needed then Sv.add x s else s in
      if spec && needed && is_stack_var x then 
        Sv.add (get_xs env x) s else s
      
    | Pget(_, x, e) -> 
      let x = L.unloc x in
      assert (is_stack_var x);
      let s = if needed then Sv.add x s else s in
      let s = if spec && needed then Sv.add (get_xs env xs) s else s in
      sct_e env ~spec ~needed:true s e
      
    | Pload(_, x, e) ->
      let x = L.unloc x in
      assert (not(is_stack_var x));
      let s = if needed then Sv.add mem s else s in
      let s = if spec && needed then Sv.add xs s else s in
      sct_e env ~spec ~needed:true (Sv.add x s) e 
 
    | Papp1 (_, e) -> sct_e env ~spec ~needed s e
    | Papp2 (_, e1, e2) -> sct_es env ~spec ~needed s [e1;e2]
    | PappN (_, es) -> sct_es env ~spec ~needed s es 
    | Pif(_,e1,e2,e3) -> sct_es env ~spec ~needed s [e1;e2;e3]

  and sct_es env ~spec ~needed s es = 
    List.fold_left (sct_e env ~spec ~needed) s es 

  let sct_lv env ~spec sO lv = 
    match lv with
    | Lnone _ -> Sv.empty, Sv.empty, false
    | Lvar x  -> 
      let x = L.unloc x in
      let needed = 
        let xs = get_xs env x in
        if is_stack_var x then
          Sv.mem x sO || Sv.mem xs sO
        else Sv.mem x sO in
      Sv.empty, Sv.singleton x, needed 
        
    | Lmem(_,x,e) -> 
      let x = L.unloc x in
      assert (not (is_stack_var x));
      let needed = Sv.mem mem sO || Sv.mem xs sO in
      sct_e env ~spec ~needed:true (Sv.singleton x) e, Sv.empty, needed
  
    | Laset(_,x,e) ->
      let x = L.unloc x in
      assert (is_stack_var x);
      let xs = get_xs env xs in
      let needed = Sv.mem x sO || Sv.mem xs sO in
      sct_e env ~spec ~needed:true Sv.empty e, Sv.empty, needed
  
  let sct_lvs env ~spec sO lvs =
    let l = List.map (sct_lv env ~spec sO) lvs in
    let needed = List.exists (fun (_,_,needed) -> needed) l in
    let to_remove = 
      List.fold_left 
        (fun to_remove (_, s, _) -> Sv.union to_remove s) Sv.empty l in
    let to_add = 
      List.fold_left 
        (fun to_add (s, _, _) -> Sv.union to_add s) Sv.empty l in
    to_add, to_remove, needed
  
  
  let pp_x msg s =
    Format.eprintf  "%s = {@[%a@]}@." msg
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements s) 
  
  let pp_X fmt (iS, iC) = 
      Format.fprintf fmt "@[<h>S = { %a }        | C = { %a }@]@ "
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements iS) 
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements iC) 
  
  let rec sct_i env i (oS, oC) = 
   (* Format.eprintf "@[<h>sct_i %a    %a@]@." 
      (Printer.pp_stmt ~debug:false) [i]
      pp_X (oS, oC); *)
  
    let x, i_desc = 
      match i.i_desc with
      | Cassgn(x,_,_,e) ->
        let doit spec sO = 
          let to_add, to_remove, needed = sct_lv env ~spec sO x in
          let x = (Sv.union to_add (Sv.diff sO to_remove)) in
          let xe = sct_e env ~spec ~needed  Sv.empty e in
       (*   pp_x "x" x;
          pp_x "xe" xe; *)
          Sv.union x xe in
  
        (doit true oS, doit false oC), i.i_desc
      
      | Copn(_, _, Expr.Ox86 (X86_instr_decl.LFENCE), _) ->
        let oC = Sv.union oS oC in
        let oC = Hv.fold (fun _x xs oC -> Sv.remove xs oC) env oC in
        (Sv.empty, Sv.remove xs oC), i.i_desc
      
      | Copn(xs, _, _, es) ->
        let doit spec sO = 
          let to_add, to_remove, needed = sct_lvs env ~spec sO xs in
          let x = (Sv.union to_add (Sv.diff sO to_remove)) in
          let xe = sct_es env ~spec ~needed  Sv.empty es in
  (*        Format.eprintf "%s@." (if spec then "Spec" else "CT");
          Format.eprintf "needed = %b@." needed;
          pp_x "x" x;
          pp_x "xe" xe; *)
          Sv.union x xe in    
        (doit true oS, doit false oC), i.i_desc
      
      | Cif (e,c1,c2) ->
        let ((iS1, iC1), c1) = sct_c env c1 (oS, oC) in
        let ((iS2, iC2), c2) = sct_c env c2 (oS, oC) in
        let needed = true in
        let iS = sct_e env ~spec:true ~needed (Sv.union iS1 iS2) e in
        let iC = sct_e env ~spec:false ~needed (Sv.union iC1 iC2) e in
        (iS, iC), Cif(e,c1,c2)
   
  
                
      | Cwhile(a,c1,e,c2) -> 
        (* c1;while e {c2; c1} *)
        let rec aux oS oC = 
          let (iS1,iC1), c1 = sct_c env c1 (oS,oC) in
          let (iS2,iC2), c2 = sct_c env c2 (iS1,iC1) in
          let needed = true in
          let iS = sct_e env ~spec:true ~needed iS2 e in
          let iC = sct_e env ~spec:false ~needed iC2 e in
          if Sv.subset iS oS && Sv.subset iC oC then
            (iS1,iC1), (* (oS,Oc), *) c1, c2
          else
            aux (Sv.union iS oS) (Sv.union iC oC) in
        let xI, c1, c2 = aux oS oC in
        xI, Cwhile(a,c1,e,c2)
  
      | Cfor _ -> assert false
  
      | Ccall _ -> assert false in
  
    x, {i_desc; i_loc = i.i_loc; i_info = x }
  
  and sct_c env c o = 
    match c with
    | [] -> o, []
    | i :: c ->
      let xc,c = sct_c env c o in
      let xi, i = sct_i env i xc in
      xi, i::c
  
  
  let rec map_info_i i = 
    let i_desc = 
      match i.i_desc with
      | Cassgn(x,t,ty,e)   -> Cassgn(x,t,ty,e)
      | Copn(xs,t,o,e)     -> Copn(xs,t,o,e) 
      | Cif(e,c1,c2)       -> Cif(e, map_info_c c1, map_info_c c2)
      | Cwhile (a,c1,e,c2) -> Cwhile(a, map_info_c c1, e, map_info_c c2)
      | Cfor _             -> assert false
      | Ccall _            -> assert false in
    {i_desc; i_loc = i.i_loc; i_info = Sv.empty, Sv.empty }
  
  and map_info_c c = 
    List.map map_info_i c
  
  let check_fun f = 
    let body = map_info_c f.f_body in
    let env = empty_env () in
    let xS = 
      Sv.fold (fun x s ->
          if is_stack_var x then Sv.add (get_xs env x) s 
          else s) (vars_fc f) (Sv.singleton xs) in 
    let (iS, iC), _body = sct_c env body (Sv.empty, Sv.empty) in
    
    let to_keep = 
      Sv.add mem (Sv.union xS (Sv.of_list f.f_args)) in
    let iS, iC = 
      Sv.inter to_keep iS, Sv.inter to_keep iC in
  
    Format.eprintf "For function %s@." f.f_name.fn_name;
   
    Format.eprintf "%a@.@."
      (Printer.pp_istmt ~debug:false pp_X) _body;
  
    Format.eprintf "dependency: %a@.@." pp_X (iS, iC);

    if Sv.mem mem iC || Sv.mem mem iS then
      Format.eprintf "ERROR: the function %s is not constant time (memory)@."
        f.f_name.fn_name;
  
    if Sv.mem xs iS then
      Format.eprintf "WARNING: speculative leakages of %s depend of xs@."
        f.f_name.fn_name;
    let check_xs _x xs = 
      if Sv.mem xs iS then
        Format.eprintf "WARNING: speculative leakages of %s depend of %a@."
          f.f_name.fn_name (Printer.pp_var ~debug:false) xs in
    Hv.iter check_xs env; 
    Format.eprintf "@.@."

end 

module V4_weak' = struct

  (* For each stack variable [x] we add a variable [#x] representing
     all values that are stored in this variable.
     For all other memory location we over approximate using a common 
     variable xs *)

  type env = var Hv.t 

  let empty_env () = Hv.create 107 

  let get_xs env x = 
    try Hv.find env x
    with Not_found ->
      let name = "#"^x.v_name in
      let xs = V.mk name x.v_kind x.v_ty x.v_dloc in
      Hv.add env x xs;
      xs

  let rec sct_e env ~needed s e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ -> s
    | Pglobal _ -> s (* since globals are never write and they address are disjoint every where no miss speculation is possible here *) 
      
    | Pvar x -> 
      let x = L.unloc x in
      let s = if needed then Sv.add x s else s in
      if needed && is_stack_var x then 
        Sv.add (get_xs env x) s else s
      
    | Pget(_, x, e) -> 
      let x = L.unloc x in
      assert (is_stack_var x);
      let s = if needed then Sv.add (get_xs env xs) (Sv.add x s) else s in
      sct_e env ~needed:true s e
      
    | Pload(_, x, e) ->
      let x = L.unloc x in
      assert (not(is_stack_var x));
      let s = if needed then Sv.add xs (Sv.add mem s) else s in
      sct_e env ~needed:true (Sv.add x s) e 
 
    | Papp1 (_, e) -> sct_e env ~needed s e
    | Papp2 (_, e1, e2) -> sct_es env ~needed s [e1;e2]
    | PappN (_, es) -> sct_es env ~needed s es 
    | Pif(_,e1,e2,e3) -> sct_es env ~needed s [e1;e2;e3]

  and sct_es env ~needed s es = 
    List.fold_left (sct_e env ~needed) s es 

  let sct_lv env sO lv = 
    match lv with
    | Lnone _ -> Sv.empty, Sv.empty, false
    | Lvar x  -> 
      let x = L.unloc x in
      let needed = 
        let xs = get_xs env x in
        if is_stack_var x then
          Sv.mem x sO || Sv.mem xs sO
        else Sv.mem x sO in
      Sv.empty, Sv.singleton x, needed 
        
    | Lmem(_,x,e) -> 
      let x = L.unloc x in
      assert (not (is_stack_var x));
      let needed = Sv.mem mem sO || Sv.mem xs sO in
      sct_e env ~needed:true (Sv.singleton x) e, Sv.empty, needed
  
    | Laset(_,x,e) ->
      let x = L.unloc x in
      assert (is_stack_var x);
      let xs = get_xs env xs in
      let needed = Sv.mem x sO || Sv.mem xs sO in
      sct_e env ~needed:true Sv.empty e, Sv.empty, needed
  
  let sct_lvs env sO lvs =
    let l = List.map (sct_lv env sO) lvs in
    let needed = List.exists (fun (_,_,needed) -> needed) l in
    let to_remove = 
      List.fold_left 
        (fun to_remove (_, s, _) -> Sv.union to_remove s) Sv.empty l in
    let to_add = 
      List.fold_left 
        (fun to_add (s, _, _) -> Sv.union to_add s) Sv.empty l in
    to_add, to_remove, needed
  
  
  let pp_x msg s =
    Format.eprintf  "%s = {@[%a@]}@." msg
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements s) 
  
  let pp_X fmt iC = 
      Format.fprintf fmt "@[C = { %a }@]@ "
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements iC) 
  
  let rec sct_i env i oC = 
    let x, i_desc = 
      match i.i_desc with
      | Cassgn(x,_,_,e) ->
        let doit sO = 
          let to_add, to_remove, needed = sct_lv env sO x in
          let x = (Sv.union to_add (Sv.diff sO to_remove)) in
          let xe = sct_e env ~needed  Sv.empty e in
          Sv.union x xe in
  
        doit oC, i.i_desc
      
      | Copn(_, _, Expr.Ox86 (X86_instr_decl.LFENCE), _) ->
        let iC = 
          Hv.fold (fun x xs s -> 
              if Sv.mem xs oC then Sv.add x (Sv.remove xs s)
              else s) env oC in
        let iC = if Sv.mem xs oC then (Sv.remove xs iC) else iC in 
        iC, i.i_desc
      
      | Copn(xs, _, _, es) ->
        let doit sO = 
          let to_add, to_remove, needed = sct_lvs env sO xs in
          let x = (Sv.union to_add (Sv.diff sO to_remove)) in
          let xe = sct_es env ~needed Sv.empty es in
          Sv.union x xe in    
        doit oC, i.i_desc
      
      | Cif (e,c1,c2) ->
        let (iC1, c1) = sct_c env c1 oC in
        let (iC2, c2) = sct_c env c2 oC in
        let iC = sct_e env ~needed:true (Sv.union iC1 iC2) e in
        iC, Cif(e,c1,c2)
         
      | Cwhile(a,c1,e,c2) -> 
        (* c1;while e {c2; c1} *)
        let rec aux oC = 
          let iC1, c1 = sct_c env c1 oC in
          let iC2, c2 = sct_c env c2 iC1 in
          let iC = sct_e env ~needed:true iC2 e in
          if Sv.subset iC oC then
            iC1, c1, c2
          else
            aux (Sv.union iC oC) in
        let xI, c1, c2 = aux oC in
        xI, Cwhile(a,c1,e,c2)
  
      | Cfor _ -> assert false
  
      | Ccall _ -> assert false in
  
    x, {i_desc; i_loc = i.i_loc; i_info = x }
  
  and sct_c env c o = 
    match c with
    | [] -> o, []
    | i :: c ->
      let xc,c = sct_c env c o in
      let xi, i = sct_i env i xc in
      xi, i::c
  
  
  let rec map_info_i i = 
    let i_desc = 
      match i.i_desc with
      | Cassgn(x,t,ty,e)   -> Cassgn(x,t,ty,e)
      | Copn(xs,t,o,e)     -> Copn(xs,t,o,e) 
      | Cif(e,c1,c2)       -> Cif(e, map_info_c c1, map_info_c c2)
      | Cwhile (a,c1,e,c2) -> Cwhile(a, map_info_c c1, e, map_info_c c2)
      | Cfor _             -> assert false
      | Ccall _            -> assert false in
    {i_desc; i_loc = i.i_loc; i_info = Sv.empty }
  
  and map_info_c c = 
    List.map map_info_i c
  
  let check_fun f = 
    let body = map_info_c f.f_body in
    let env = empty_env () in
    let xS = 
      Sv.fold (fun x s ->
          if is_stack_var x then Sv.add (get_xs env x) s 
          else s) (vars_fc f) (Sv.singleton xs) in
    let iC, _body = sct_c env body Sv.empty (*xS*) in
    
    let to_keep = 
      Sv.add mem (Sv.union xS (Sv.of_list f.f_args)) in
    let iC = Sv.inter to_keep iC in
  
    Format.eprintf "For function %s@." f.f_name.fn_name;
   
    Format.eprintf "%a@.@."
      (Printer.pp_istmt ~debug:false pp_X) _body;
  
    Format.eprintf "dependency: %a@.@." pp_X iC;

    if Sv.mem mem iC then
      Format.eprintf "ERROR: the function %s is not constant time (memory)@."
        f.f_name.fn_name;
  
    if Sv.mem xs iC then
      Format.eprintf "WARNING: speculative leakages of %s depend of xs@."
        f.f_name.fn_name;
    let check_xs _x xs = 
      if Sv.mem xs iC then
        Format.eprintf "WARNING: speculative leakages of %s depend of %a@."
          f.f_name.fn_name (Printer.pp_var ~debug:false) xs in
    Hv.iter check_xs env; 
    Format.eprintf "@.@."

end 

module V4_weak_simple = struct

  let rec sct_e ~needed s e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ -> s
    | Pglobal _ -> s (* since globals are never write and they address are disjoint every where no miss speculation is possible here *) 
      
    | Pvar x -> 
      let x = L.unloc x in
      if needed then Sv.add x s else s 
      
    | Pget(_, x, e) -> 
      let x = L.unloc x in
      assert (is_stack_var x);
      let s = if needed then (Sv.add x s) else s in
      sct_e ~needed:true s e
      
    | Pload(_, x, e) ->
      let x = L.unloc x in
      assert (not(is_stack_var x));
      let s = if needed then Sv.add xs (Sv.add mem s) else s in
      sct_e ~needed:true (Sv.add x s) e 
 
    | Papp1 (_, e) -> sct_e ~needed s e
    | Papp2 (_, e1, e2) -> sct_es ~needed s [e1;e2]
    | PappN (_, es) -> sct_es ~needed s es 
    | Pif(_,e1,e2,e3) -> sct_es ~needed s [e1;e2;e3]

  and sct_es ~needed s es = 
    List.fold_left (sct_e ~needed) s es 

  let sct_lv sO lv = 
    match lv with
    | Lnone _ -> Sv.empty, Sv.empty, false
    | Lvar x  -> 
      let x = L.unloc x in
      Sv.empty, (if is_stack_var x then Sv.empty else Sv.singleton x), Sv.mem x sO
        
    | Lmem(_,x,e) -> 
      let x = L.unloc x in
      assert (not (is_stack_var x));
      let needed = Sv.mem mem sO || Sv.mem xs sO in
      sct_e ~needed:true (Sv.singleton x) e, Sv.empty, needed
  
    | Laset(_,x,e) ->
      let x = L.unloc x in
      assert (is_stack_var x);
      sct_e ~needed:true Sv.empty e, Sv.empty, Sv.mem x sO

  
  let sct_lvs sO lvs =
    let l = List.map (sct_lv sO) lvs in
    let needed = List.exists (fun (_,_,needed) -> needed) l in
    let to_remove = 
      List.fold_left 
        (fun to_remove (_, s, _) -> Sv.union to_remove s) Sv.empty l in
    let to_add = 
      List.fold_left 
        (fun to_add (s, _, _) -> Sv.union to_add s) Sv.empty l in
    to_add, to_remove, needed
  
  
  let pp_x msg s =
    Format.eprintf  "%s = {@[%a@]}@." msg
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements s) 
  
  let pp_X fmt iC = 
      Format.fprintf fmt "@[C = { %a }@]@ "
        (Printer.pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements iC) 
  
  let rec sct_i i oC = 
    let x, i_desc = 
      match i.i_desc with
      | Cassgn(x,_,_,e) ->
        let doit sO = 
          let to_add, to_remove, needed = sct_lv sO x in
          let x = (Sv.union to_add (Sv.diff sO to_remove)) in
          let xe = sct_e ~needed  Sv.empty e in
          Sv.union x xe in
  
        doit oC, i.i_desc
      
      | Copn(_, _, Expr.Ox86 (X86_instr_decl.LFENCE), _) ->
  
        oC, i.i_desc
      
      | Copn(xs, _, _, es) ->
        let doit sO = 
          let to_add, to_remove, needed = sct_lvs sO xs in
          let x = (Sv.union to_add (Sv.diff sO to_remove)) in
          let xe = sct_es ~needed Sv.empty es in
          Sv.union x xe in    
        doit oC, i.i_desc
      
      | Cif (e,c1,c2) ->
        let (iC1, c1) = sct_c c1 oC in
        let (iC2, c2) = sct_c c2 oC in
        let iC = sct_e ~needed:true (Sv.union iC1 iC2) e in
        iC, Cif(e,c1,c2)
         
      | Cwhile(a,c1,e,c2) -> 
        (* c1;while e {c2; c1} *)
        let rec aux oC = 
          let iC1, c1 = sct_c c1 oC in
          let iC2, c2 = sct_c c2 iC1 in
          let iC = sct_e ~needed:true iC2 e in
          if Sv.subset iC oC then
            iC1, c1, c2
          else
            aux (Sv.union iC oC) in
        let xI, c1, c2 = aux oC in
        xI, Cwhile(a,c1,e,c2)
  
      | Cfor _ -> assert false
  
      | Ccall _ -> assert false in
  
    x, {i_desc; i_loc = i.i_loc; i_info = x }
  
  and sct_c c o = 
    match c with
    | [] -> o, []
    | i :: c ->
      let xc,c = sct_c c o in
      let xi, i = sct_i i xc in
      xi, i::c
  
  
  let rec map_info_i i = 
    let i_desc = 
      match i.i_desc with
      | Cassgn(x,t,ty,e)   -> Cassgn(x,t,ty,e)
      | Copn(xs,t,o,e)     -> Copn(xs,t,o,e) 
      | Cif(e,c1,c2)       -> Cif(e, map_info_c c1, map_info_c c2)
      | Cwhile (a,c1,e,c2) -> Cwhile(a, map_info_c c1, e, map_info_c c2)
      | Cfor _             -> assert false
      | Ccall _            -> assert false in
    {i_desc; i_loc = i.i_loc; i_info = Sv.empty }
  
  and map_info_c c = 
    List.map map_info_i c
  
  let check_fun f = 
    let body = map_info_c f.f_body in

    let iC, _body = sct_c body Sv.empty in
    
    let to_keep = 
      Sv.add mem (Sv.of_list f.f_args) in
    let iC = Sv.inter to_keep iC in
  
    Format.eprintf "For function %s@." f.f_name.fn_name;
   
    Format.eprintf "%a@.@."
      (Printer.pp_istmt ~debug:false pp_X) _body;
  
    Format.eprintf "dependency: %a@.@." pp_X iC;

    if Sv.mem mem iC then
      Format.eprintf "ERROR: the function %s is not constant time (memory)@."
        f.f_name.fn_name;
     
    Format.eprintf "@.@."

end 


let check_fun model f = 
  match model with
  | V1 -> V1.check_fun f
  | V4 -> V4.check_fun f
  | V4_weak -> V4_weak_simple.check_fun f

  




  


