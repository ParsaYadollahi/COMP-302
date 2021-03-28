(* Q0  : Get familiar with the external syntax of MiniML *)
let parse_tests : (string * (string, exp) either) list = [
    (* Provide your tests for the parser *)
  ("1;", Right (Int 1))
]


let free_vars_tests : (exp * name list) list = [
  (Int 10, [])
]

(* Q1  : Find the free variables in an expression *)
let rec free_vars (e : exp) : name list = match e with
  | Bool x -> []
  | Int x -> []
  | Var x -> [x]
  | Apply (el1, el2) ->
      let freeVars1 = free_vars el1 in
      let freeVars2 = free_vars el2 in
      union freeVars1 freeVars2;
  | Anno (el1, el2) -> free_vars el1
  | If (el1, el2, el3) ->
      let freeVars1 = free_vars el1 in
      let freeVars2 = free_vars el2 in
      let freeVars3 = free_vars el3 in
      union freeVars1
        (union freeVars2 freeVars3)
  | Primop (_,el2) | Tuple el2 ->
      List.fold_left
        (fun x y ->
           let freeVarsY = free_vars y in
           union x (freeVarsY)
        ) [] el2
  | Rec (el1, _, el3) | Fn (el1, _, el3) ->
      let deleteVars = free_vars el3 in
      delete [el1] deleteVars
  | Let (l, el) ->
      let rec aux l1 l2 l3 = match l1 with
        | [] -> (l2, l3)
        | x::remainder -> match x with
          | Valtuple (el1, el2) ->
              let union1 = union l2 el2 in
              let union2 = union l3 (delete l2 (free_vars el1)) in
              aux remainder (union1) (union2)
          | Val(el1, el2) | ByName (el1, el2) ->
              let deleteVars = delete l2 (free_vars el1) in
              let union1 = union l2 [el2] in
              let union2 = union l3 (deleteVars) in
              aux remainder (union1) (union2) in
      let (t, f) = aux l [] [] in
      let delFreeVars = delete t (free_vars el) in
      union f (delFreeVars)


let unused_vars_tests : (exp * name list) list = [
]

(* Q2  : Check variables are in use *)
let rec unused_vars (e : exp) : name list = match e with
  | Rec (var1, var2, var3) -> unused_vars var3
  | If (var1, var2, var3) ->
      let freeVars1 = free_vars var1 in
      let freeVars2 = free_vars var2 in
      let freeVars3 = free_vars var3 in
      let arr_unused = freeVars2 @ freeVars3 in
      freeVars1 @ (arr_unused)
  | Fn (var1, var2, var3) ->
      let unusedVars = (unused_vars var3) in
      let freeVars = (free_vars var3) in
      if member var1 freeVars
      then unusedVars
      else
        var1 :: unusedVars;
  | Primop (_, vars) | Tuple (vars) ->
      List.fold_left (fun var1 var2 ->
          let unusedVars2 = unused_vars var2 in
          var1 @ (unusedVars2)) [] vars
  | Apply (var1, var2) ->
      let unusedVars1 = unused_vars var1 in
      let unusedVars2 = unused_vars var2 in
      (unusedVars1) @ (unusedVars2)
  | Anno (var1, var2) -> unused_vars var1
  | Let (l, vars) ->
      let rec delSetFunction delSet set = match set with
        | [] -> []
        | x :: remainder ->
            if member x delSet then
              let deleteEl1 = (delete [x] delSet) in
              delSetFunction deleteEl1 remainder
            else
              let deleteEl2 = delSetFunction delSet in
              x :: deleteEl2 remainder in
      let rec aux l1 l2 l3 = match l1 with
        | [] -> (l2, l3)
        | x:: remainder -> match x with
          | Valtuple (var1, var2) ->
              let freeVars1 = free_vars var1 in
              let unusedVars1 = unused_vars var1 in
              let delFunctionVar = delSetFunction (freeVars1) (l2) in
              let concatUnusedVars = (l3 @ unusedVars1) in
              let concatDelVar = delFunctionVar @ var2 in
              aux remainder concatDelVar
                concatUnusedVars;
          | Val(var1, var2)  | ByName (var1, var2) ->
              let freeVars1 = free_vars var1 in
              let unusedVars1 = unused_vars var1 in
              let concatUnusedVars = l3 @ unusedVars1 in
              let delFunctionVar = delSetFunction (freeVars1) (l2) in
              let concatDelVar = delFunctionVar @ [var2] in
              aux remainder concatDelVar
                concatUnusedVars;
      in let (u1, u2) = aux l [] [] in
      let delSetFuncVar = delSetFunction (free_vars vars) u1 in
      let unusedVars = unused_vars vars in
      delSetFuncVar @ unusedVars @ u2
  | _ -> []



let subst_tests : (((exp * name) * exp) * exp) list = [
]

(* Q3  : Substitute a variable *)
let rec subst ((e', x) : exp * name) (e : exp) : exp =
  match e with
  | Var y ->
      if x = y then
        e'
      else
        Var y

  | Int _ | Bool _ -> e
  | Primop (po, es) -> Primop (po, List.map (subst (e', x)) es)
  | If (e1, e2, e3) -> If (subst (e', x) e1, subst (e', x) e2, subst (e', x) e3)
  | Tuple es -> Tuple (List.map (subst (e', x)) es)
  | Anno (e, t) -> Anno (subst (e', x) e, t)

  | Apply (e1, e2) ->
      let subst1 = subst (e', x) e1 in
      let subst2 = subst (e', x) e2 in
      Apply (subst1, subst2)
  | Fn (y, t, e) ->
      if y != x then
        let subEl = subst (e', x) in
        let freeVar = free_vars e' in
        if member y freeVar then
          let freshVar = fresh_var y in
          let subVar = subEl (subst (Var (freshVar), y) e) in
          Fn (freshVar, t, subVar)
        else
          Fn (y, t, subEl e)
      else
        Fn (y, t, e)
  | Rec (y, t, e) ->
      if y != x then
        let subEl = subst (e', x) in
        let freeVars = free_vars e' in
        if member y freeVars then
          let freshVar = fresh_var y in
          let subVar = subEl (subst (Var (freshVar), y) e) in
          Rec (freshVar, t, subVar)
        else
          Rec (y, t, subEl e)
      else
        Rec (y, t, e)



  | Let (ds, e2) -> raise NotImplemented
      (* let f = free_vars e' in
      let replacing list expr =
        let rec replacing2 list2 expr2 = match list2 with
          | [] -> expr2
          | i::t -> let (b, c) = i in replacing2 t (subst (b, c) expr2)
        in replacing2 (List.rev list) expr in
      let rec helper2 l1 l2 replace track = (match l1 with
          | [] ->  (l2, replace, track)
          | h::t -> match h with
            | Val (y, n) ->
                if n = x then (if not(track) then (helper2 t
                                                     ( l2 @ [Val (  (
                                                           subst (e', x)
                                                             (replacing replace y)
                                                         ), n) ]      )
                                                     replace true) else
                                 (helper2 t ( l2 @ [Val (  ( replacing replace y
                                                           ), n) ]) replace true))
                else if member n f then let z = fresh_var n in helper2 t
                    ( if not(track) then (
                          l2 @ [Val (( subst (e', x)(replacing replace y)
                                     ), z) ]) else ( l2 @ [Val ((
                        replacing replace y ), z) ]) ) (replace @ [(Var (z), n)])
                    track
                else helper2 t ( if not(track) then ( l2 @ [Val (  (
                    subst (e', x) (replacing replace y) ), n) ]) else
                      ( l2 @ [Val (( replacing replace y ), n) ]) ) replace track
            | Valtuple (y,n) ->
                let rec find l1x l2x l3x trk = (match l1x with
                    | [] -> (l2x, l3x, trk)
                    | h::t ->
                        if h = x then find t (l2x @ [x]) l3x true else
                        if member h f then let z = fresh_var h in
                          find t (l2x @ [z]) (l3x @ [(Var(z), h)]) trk
                        else find t (l2x @ [h]) l3x trk )
                in let (ax, bx, tr1) = find n [] [] false in
                helper2 t  ( if not(track) then ( l2 @ [Valtuple (  (
                    subst (e', x) (replacing replace y) ), ax) ])
                    else ( l2 @ [Valtuple (( replacing replace y ), ax) ]) )
                  (replace @ bx) (track || tr1)
            | ByName (y, n) ->
                if n = x then (if not(track) then (helper2 t ( l2 @ [ByName ( (
                    subst (e', x) (replacing replace y) ), n) ]) replace true)
                   else (helper2 t ( l2 @ [ByName (  ( replacing replace y
                                                     ), n) ]) replace true)) else
                if member n f then let z = fresh_var n in helper2 t
                    (if not(track) then ( l2 @ [ByName (( subst (e', x)
                                                            (replacing replace y)
                                                        ), z) ]      )
                     else ( l2 @ [ByName (( replacing replace y ), z) ] ) )
                    (replace @ [(Var (z), n)]) track
                else helper2 t (if not(track) then ( l2 @ [ByName (  (
                    subst (e', x)(replacing replace y) ), n) ])
                   else  ( l2 @ [ByName (( replacing replace y ), n) ]))
                    replace track ) in let (g,h,tr) = helper2 ds [] [] false in
      if not tr then Let (g, subst (e', x) (replacing h e2 ) )
      else Let (g, (replacing h e2)) *)

(* TESTING SUBST OUT *)
(* let subst ( Int 5 , "x") ( If ( Bool ( true ) , Var "x", Var "y") ) ; *)

let eval_tests : (exp * exp) list = [
]


  (* Useful helper function *)
let replacing l1 var =
  let rec aux l2 var2 = match l2 with
    | [] -> var2
    | x :: remainder ->
        let (b, c) = x in
        let substEl = subst (b, c) in
        let rem = (substEl var2) in
        aux remainder rem
  in
  let revListL1 = (List.rev l1) in
  aux revListL1 var

(* Q4  : Evaluate an expression in big-step *)
let rec eval : exp -> exp =
  (* do not change the code from here *)
  let bigstep_depth = ref 0 in
  fun e ->
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "eval (" ^ Print.exp_to_string e ^ ")\n");
    incr bigstep_depth;
  (* to here *)
    let result =
      match e with
      | Int _ | Bool _ -> e
      | Tuple es -> Tuple (List.map eval es)
      | If (e1, e2, e3) ->
          begin match eval e1 with
            | Bool b ->
                if b then
                  eval e2
                else
                  eval e3
            | _ -> stuck "Condition for if expression should be of the type bool"
          end
      | Anno (e, _) -> eval e     (* types are ignored in evaluation *)
      | Var x -> stuck ("Free variable \"" ^ x ^ "\" during evaluation")

      | Fn (x, t, e) ->
          Fn (x, t, e)
      | Apply (e1, e2) ->
          let evalE1 = eval e1 in
          match evalE1 with
          | Fn (el1, el2, el3) ->
              let evalE2 = eval e2 in
              let substE2 = subst (evalE2, el1) in
              eval (substE2 el3 )
          | _ -> stuck ("Didn't evaluate to a function")


          | Rec (f, t, e) ->
              let r = Rec (f,t, e) in
              let substR = subst ((r), f) in
              eval (substR e)

          | Primop (And, es) -> Bool (
              List.fold_left (
                fun el1 el2 ->
                  let evalEl2 = eval el2 in
                  match evalEl2 with
                  | Bool bool ->
                      if bool then
                        el1
                      else
                        bool
                  | _ -> stuck ("Did not get a boolean")
              ) true es  )
          | Primop (Or, es) -> Bool (
              List.fold_left (
                fun el1 el2 ->
                  let evalEl2 = eval el2 in
                  match evalEl2 with
                  | Bool bool ->
                      if bool then
                        bool
                      else
                        el1
                  | _ -> stuck ("Did not get a boolean")
              ) true es  )
          | Primop (op, es) ->
              let vs = List.map eval es in
              begin match eval_op op vs with
                | None -> stuck "Bad arguments to primitive operation"
                | Some v -> v
              end

          | Let (ds, e) ->
              let rec aux el1 el2 = match el1 with
                | [] -> el2
                | x :: remainder -> match x with
                  | Val (var1, var2)  ->
                      let replace = replacing el2 var1 in
                      let evalReplace = [eval (replacing el2 var1), var2] in
                      let concatReplace = el2 @ evalReplace in
                      aux remainder (concatReplace)
                  | ByName (var1, var2) ->
                      let replace = replacing el2 var1 in
                      let addReplace = [replace, var2] in
                      let concatReplace = el2 @ addReplace in
                      aux remainder (concatReplace)
                  | Valtuple (var1, var2) ->
                      let evalVar1 = eval var1 in
                      match evalVar1 with
                      | Tuple (l1) ->
                          let lenList1 = List.length l1 in
                          let lenList2 = List.length var2 in
                          if  lenList1 = lenList2 then
                            stuck "length of Tuple is wring"
                          else
                            let rec substTuples l1 l2 repl = match (l1, l2) with
                              | ([], _) -> repl
                              | (x_l1::remainderL1, y_l2::remainderL2) ->
                                  let replace = replacing repl y_l2 in
                                  let addReplace = [replace, x_l1] in
                                  let concatReplace = repl @ addReplace in
                                  substTuples remainderL1 remainderL2 concatReplace
                              | _ -> repl
                            in let rep = substTuples var2 l1 el2 in
                            aux remainder rep
                      | _ ->  stuck "Needed a tuple"
              in let repl = aux ds [] in
              let el = replacing repl e
              in eval el
    in
  (* do not change the code from here *)
    decr bigstep_depth;
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "result of eval (" ^ Print.exp_to_string e ^ ") = "
         ^ Print.exp_to_string result ^ "\n");
  (* to here *)
    result


let infer_tests : ((context * exp) * typ) list = [
]

(* Q5  : Type an expression *)
(* Q7* : Implement the argument type inference
         For this question, move this function below the "unify". *)
let infer (ctx : context) (e : exp) : typ = raise NotImplemented


let unify_tests : ((typ * typ) * unit) list = [
]

(* find the next function for Q5 *)
(* Q6  : Unify two types *)
let unify (ty1 : typ) (ty2 : typ) : unit = raise NotImplemented


(* Now you can play with the language that you've implemented! *)
let execute (s: string) : unit =
  match P.parse s with
  | Left s -> print_endline ("parsing failed: " ^ s)
  | Right e ->
      try
       (* first we type check the program *)
        ignore (infer (Ctx []) e);
        let result = eval e in
        print_endline ("program is evaluated to: " ^ Print.exp_to_string result)
      with
      | NotImplemented -> print_endline "code is not fully implemented"
      | Stuck s -> print_endline ("evaluation got stuck: " ^ s)
      | NotFound -> print_endline "variable lookup failed"
      | TypeError s -> print_endline ("type error: " ^ s)
      | e -> print_endline ("unknown failure: " ^ Printexc.to_string e)


(************************************************************
 *                     Tester template:                     *
 *         Codes to test your interpreter by yourself.      *
 *         You can change these to whatever you want.       *
 *                We won't grade these codes                *
 ************************************************************)
let list_to_string el_to_string l : string =
  List.fold_left
    begin fun acc el ->
      if acc = "" then
        el_to_string el
      else
        acc ^ "; " ^ el_to_string el
    end
    ""
    l
  |> fun str -> "[" ^ str ^ "]"

let run_test name f ts stringify : unit =
  List.iteri
    begin fun idx (input, expected_output) ->
      try
        let output = f input in
        if output <> expected_output then
          begin
            print_string (name ^ " test #" ^ string_of_int idx ^ " failed\n");
            print_string (stringify output ^ " <> " ^ stringify expected_output);
            print_newline ()
          end
      with
      | exn ->
          print_string (name ^ " test #" ^ string_of_int idx ^ " raised an exception:\n");
          print_string (Printexc.to_string exn);
          print_newline ()
    end
    ts

let run_free_vars_tests () : unit =
  run_test "free_vars" free_vars free_vars_tests (list_to_string (fun x -> x))

let run_unused_vars_tests () : unit =
  run_test "unused_vars" unused_vars unused_vars_tests (list_to_string (fun x -> x))

let run_subst_tests () : unit =
  run_test "subst" (fun (s, e) -> subst s e) subst_tests Print.exp_to_string

let run_eval_tests () : unit =
  run_test "eval" eval eval_tests Print.exp_to_string

(* You may want to change this to use the unification (unify) instead of equality (<>) *)
let run_infer_tests () : unit =
  run_test "infer" (fun (ctx, e) -> infer ctx e) infer_tests Print.typ_to_string

let run_unify_tests () : unit =
  run_test "unify" (fun (ty1, ty2) -> unify ty1 ty2) unify_tests (fun () -> "()")

let run_all_tests () : unit =
  run_free_vars_tests ();
  run_unused_vars_tests ();
  run_subst_tests ();
  run_eval_tests ();
  run_infer_tests ();
  run_unify_tests ()
