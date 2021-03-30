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



  | Let (ds, e2) ->
      let f = free_vars e' in
      let replacing list expr =
        let rec aux list2 el2 = match list2 with
          | [] -> el2
          | head :: t ->
              let (e1, e2) = head in
              let substEl = subst (e1, e2) in
              let newEl2 = substEl el2 in
              aux t (newEl2)
        in aux (List.rev list) expr in
      let rec aux2 list1 list2 repl track = (
        match list1 with
        | [] ->  (list2, repl, track)
        | head :: remainder -> match head with
          | Val (y, n) ->
              let memNF = member n f in
              let replY = replacing repl y in
              if n = x then (
                if not(track) then (
                  let substEl = subst (e', x) (replY) in
                  let valSubst = [Val (substEl, n)] in
                  let concatList2 = list2 @ valSubst in
                  aux2 remainder concatList2 repl true
                )
                else (
                  let valSubst = [Val (  ( replY ), n)] in
                  let concatList2 = list2 @ valSubst in
                  aux2 remainder concatList2 repl true
                )
              )
              else if memNF then (
                let z = fresh_var n in
                let param = (
                  if not(track) then
                    let substEl = subst (e', x)(replY) in
                    let valSubst = [Val (substEl, z) ] in
                    let concatList2 = list2 @ valSubst in
                    concatList2
                  else (
                    let valRepl = [Val (replY, z) ] in
                    let concatList2 = list2 @ valRepl in
                    let varZ = Var (z), n in
                    let concatRepl = repl @ [varZ] in
                    concatList2
                  )
                ) in
                let concatReplace = repl @ [(Var (z), n)] in
                aux2 remainder param concatReplace track
              )
              else (
                aux2 remainder (
                  if not(track) then (
                    let substEl = subst (e', x) (replY) in
                    let valSubst = Val ((substEl), n) in
                    let concatList2 = list2 @ [valSubst] in
                    concatList2
                  )
                  else (
                    let replaceY = replacing repl y in
                    let valReplace = Val ((replaceY), n) in
                    let concatList2 = list2 @ [valReplace] in
                    concatList2
                  )
                )
                  repl track
              )
          | Valtuple (y,n) ->
              let rec find l1x l2x l3x trk = (match l1x with
                  | [] -> (l2x, l3x, trk)
                  | head :: remainder ->
                      let memHead = member head f in
                      if head = x then (
                        let concatX = l2x @ [x] in
                        find remainder concatX l3x true
                      )
                      else (
                        if memHead then (
                          let z = fresh_var head in
                          let concatZ = l2x @ [z] in
                          let varZ = (Var(z), head) in
                          let concatVarZ = l3x @ [varZ] in
                          find remainder concatZ concatVarZ trk
                        )
                        else (
                          let concatHead = l2x @ [head] in
                          find remainder concatHead l3x trk
                        )
                      )
                ) in
              let (ax, bx, tr1) =
                find n [] [] false in
              let replBX = repl @ bx in
              let trackOrTr1 = track || tr1 in
              let param = (
                let replY = replacing repl y in
                if not(track) then (
                  let substY = subst (e', x) (replY) in
                  let valTupleSubstY = Valtuple (( substY ), ax) in
                  let concatvalTupleSubstY = list2 @ [valTupleSubstY] in
                  concatvalTupleSubstY
                )
                else (
                  let valTupleReplY = Valtuple (( replY ), ax) in
                  let concatValTupleReplY = list2 @ [valTupleReplY] in
                  concatValTupleReplY
                )
              ) in
              aux2 remainder param replBX trackOrTr1
          | ByName (y, n) ->
              let replY = replacing repl y in
              let substEl = subst (e', x) (replY) in
              if n = x then (
                if not(track) then (
                  let byNameSubst = ByName ( ( substEl ), n) in
                  let concatbyNameSubst = list2 @ [byNameSubst] in
                  aux2 remainder concatbyNameSubst repl true
                )
                else (
                  let byNameReplY = ByName (  ( replY ), n) in
                  let concatByNameReplY = list2 @ [byNameReplY] in
                  aux2 remainder concatByNameReplY repl true
                )
              ) else (
                let memNF = member n f in
                if memNF then (
                  let z = fresh_var n in
                  let varZN = (Var (z), n) in
                  let concatReplVarZN = repl @ [varZN] in
                  let param = (
                    if not(track) then (
                      let byNameSubstZ = ByName (( substEl ), z) in
                      let concatbyNameSubstZ = list2 @ [byNameSubstZ] in
                      concatbyNameSubstZ
                    ) else (
                      let byNameReplYZ = ByName (( replY ), z) in
                      let concatByNameReplYZ = list2 @ [byNameReplYZ] in
                      concatByNameReplYZ
                    )
                  ) in
                  aux2 remainder param concatReplVarZN track
                ) else (
                  let param = (
                    if not(track) then (
                      let byNameSubstEl = ByName ( ( substEl ),n) in
                      let concatbyNameSubstEl = list2 @ [byNameSubstEl] in
                      concatbyNameSubstEl
                    ) else (
                      let byNameReplY = ByName (( replY ), n) in
                      let concatbyNameReplY = list2 @ [byNameReplY] in
                      concatbyNameReplY
                    )
                  ) in
                  aux2 remainder param repl track
                )
              )
      ) in
      let (g,h,tr) = aux2 ds [] [] false in
      let replHE2 = replacing h e2 in
      if not tr then (
        let substReplHE2 = subst (e', x) (replHE2) in
        Let (g, substReplHE2)
      ) else (
        Let (g, replHE2)
      )

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

let unify_tests : ((typ * typ) * unit) list = [
]

(* find the next function for Q5 *)
(* Q6  : Unify two types *)
let rec unify (ty1 : typ) (ty2 : typ) : unit =
  let rec aux1 type1 any1 = match type1 with
    | TInt -> true
    | TBool -> true
    | TArrow (typeOne, typeTwo) ->
        (aux1 typeOne any1);
        (aux1 typeTwo any1)
    | TProduct (l1) ->
        List.for_all (
          fun el -> aux1 el any1
        ) l1
    | TVar var ->
        if var = any1 then
          type_fail "Fail in the free variables"
        else
          let nonVar = !var in
          match (nonVar) with
          | None -> true
          | Some var' ->
              aux1 var' any1
  in
  let rec aux2 bool type1 any = match type1 with
    | TInt -> true
    | TBool -> true
    | TArrow (typeOne, typeTwo) ->
        (aux2 true typeOne any);
        (aux2 true typeTwo any)
    | TProduct (l1) ->
        List.for_all (fun el -> aux2 true el any) l1
    | TVar var ->
        if var = any then
          bool &&
          (type_fail "Fail in the free variables")
        else
          let nonVar = !var in
          match (nonVar) with
          | None -> true
          | Some var' ->
              aux2 bool var' any
  in
  if typ_eq ty1 ty2 then
    ()
  else
    match (ty1, ty2) with
    | TVar var, TVar var' -> (
        match (!var, !var') with
        | Some (el), Some (el') -> unify el el'
        | Some (el'), None ->
            let comp = aux2 false el' var' in
            if comp then
              var':= !var
            else
              ()
        | None, Some (gy')  ->  if aux2 false gy' var then  var := !var' else ()
        | None, None ->
            let comp = var != var' in
            if comp then
              let tVar = TVar var' in
              var := Some tVar
            else
              ()
      )
    | TVar var, type1 -> (
        match !var with
        | Some el -> unify el type1
        | None ->
            let comp = aux1 type1 var in
            if comp then
              var := Some (type1)
            else
              type_fail "Fail in the free variables"
      )
    | type1, TVar var ->
        ( match !var with
          | Some el -> unify el type1
          | None ->
              let comp = aux1 type1 var in
              if comp then
                var := Some type1
              else
                type_fail "Fail in the free variables"
        )
    | TArrow (type1, type2), TArrow (s1, s2) ->
        unify type1 s1;
        unify type2 s2
    | TProduct (list1'), TProduct (list2') ->
        let lenList1 = List.length list1' in
        let lenList2 = List.length list2' in
        if  lenList1 = lenList2 then
          type_fail "Length of Tuples are unequal"
        else
          let rec aux3 list1 list2 = match (list1, list2) with
            | [], [] -> ()
            | (list1Head::list1Remainder), (list2Head::list2Remainder) ->
                unify list1Head list2Head;
                aux3 list1Remainder list2Remainder
            | _ -> ()
          in (aux3 list1' list2')
    | _ -> type_fail "Error - Was unable to Unify!"


(* Q5  : Type an expression *)
(* Q7* : Implement the argument type inference
         For this question, move this function below the "unify". *)
let rec infer (ctx : context) (e : exp) : typ =  match e with

  | Int _ -> TInt
  | Bool _ -> TBool
  | If (el1, el2, el3) ->
      let unify1 = infer ctx el1 in
      let unify2 = infer ctx el2 in
      let unify3 = infer ctx el3 in
      unify unify1 TBool;
      unify unify2 unify3;
      unify2
  | Primop (o, l1) -> (match o with
      | Negate -> (match l1 with
          | [x] -> (
              let inferEl = infer ctx x in
              unify inferEl TInt;
              TInt
            )
          | _ ->
              type_fail "Error - Cannot negate: missinig arguments")
      | Or | And -> (
          if (
            List.for_all (
              fun el -> (
                  let inferEl = infer ctx el in
                  unify inferEl TBool;
                  true
                )
            ) l1
          ) then
            TBool
          else
            type_fail "Error - Not all arguments are booleans"
        )
      | Equals | NotEquals | LessThan | GreaterEqual | LessEqual | GreaterThan -> (
          if (
            List.for_all (
              fun el -> (
                  let inferEl = infer ctx el in
                  unify inferEl TInt;
                  true
                )
            ) l1
          )
          then
            TBool
          else
            type_fail "Error - Not all arguments are integers"
        )
      | Plus | Minus | Times | Div -> (
          if (
            List.for_all (
              fun x -> (
                  let inferEl = infer ctx x in
                  unify inferEl TInt;
                  true
                )
            ) l1
          )
          then
            TInt
          else
            type_fail "Error - Not all arguments are integers")
    )


  | Tuple tList -> (
      let t = List.fold_left (
          fun el1 el2 -> (
              let inferElY = infer ctx el2 in
              let concatInferElY = el1 @ [inferElY] in
              concatInferElY
            )
        )
          [] tList in
      TProduct (t)
    )

  | Fn (el1, el2, el3) -> (
      match el2 with
      | Some (type1) ->
          let extendType = el1, type1 in
          let inferExtend = extend ctx (extendType) in
          let inferEl = infer inferExtend el3 in
          TArrow (
            type1, inferEl
          )
      | None ->
          let extendctx = el1, fresh_tvar() in
          let inferAny = extend ctx extendctx in
          let inferEl3 = infer inferAny el3 in
          let inferEl1 = infer inferAny (Var el1) in
          TArrow (
            inferEl1 ,
            inferEl3
          )
    )
  | Rec (el1, el2, el3) -> el2
  | Let (li,e1) ->
      let rec aux map key =
        let Ctx(m) = map in
        match m with
        | [] -> false
        | (t, _)::remainder ->
            if t = key then
              true
            else
              aux (Ctx (remainder)) key
      in
      let rec fold_ex list1 list2 repl =
        match list1 with
        | [] -> (list2, repl)
        | x :: remainder -> (
            match x with
            | Val (el1, el2) | ByName (el1, el2) -> (
                if aux list2 el2 then (
                  let naz = fresh_var el2 in
                  let replaceEl1 = replacing repl el1 in
                  let inferEl1 = infer list2 replaceEl1 in
                  let extendInfer =  naz, inferEl1 in
                  let extendList2 = extend list2 (extendInfer) in
                  let elArray = [(Var (naz)), el2] in
                  let concatElRepl = repl @ elArray in
                  fold_ex remainder extendList2 concatElRepl
                )
                else (
                  let replace = replacing repl el1 in
                  let inferList2 = infer list2 replace in
                  let extendInfer = el2, inferList2 in
                  let extendList2 = extend list2 (extendInfer) in
                  fold_ex remainder extendList2 repl
                )
              )
            | Valtuple (l1, l2) -> (
                let replace = replacing repl l1 in
                let matching = infer list2 replace in
                match matching with
                | TProduct (l3) ->
                    let lenList2 = List.length l2 in
                    let lenList3 = List.length l3 in
                    if lenList2 = lenList3 then
                      type_fail "Error - Size of tuples must be equal"
                    else let rec aux2 l1x l2x l3x rep =
                           match (l1x, l2x) with
                           | ([], _) -> (l3x, rep)
                           | (head::tail), (head2::tail2) ->
                               if aux l3x head then (
                                 let gz = fresh_var head in
                                 let extendL3x = extend l3x (gz,head2) in
                                 let gzArray = [((Var (gz)), head)] in
                                 let concatgxArray = (rep @  gzArray) in
                                 aux2 tail tail2 extendL3x concatgxArray
                               )
                               else (
                                 let extendL3x = extend l3x (head, head2) in
                                 aux2 tail tail2 extendL3x rep
                               )
                           | _ -> (l3x,rep) in
                      let (l3x', repl2) = aux2 l2 l3 list2 repl in
                      fold_ex remainder l3x' repl2
                | _ -> type_fail "Error - Please give a tuple" ) ) in
      let (list2', repl2) = fold_ex li ctx [] in
      let replaceRepl2 = replacing repl2 e1 in
      infer list2' replaceRepl2
  | Apply (el1, el2) -> (
      let matchInfer = infer ctx el1 in
      match matchInfer with
      | TArrow (type1, type2) -> (
          let inferEl2 = infer ctx el2 in
          unify inferEl2 type1;
          type2
        )
      | _ -> type_fail "Error - No function provided, needed to apply arguments")
  | Var (var) -> (
      let matchCTX = ctx_lookup ctx var in
      try match matchCTX with
        | TVar (l) -> (
            let nonL = !l in
            match nonL with
            | Some (l') -> l'
            | None -> ctx_lookup ctx var
          )
        | _ -> ctx_lookup ctx var
      with NotFound -> type_fail "Error - Free variable" )
  | Anno (var1, type1) ->
      let inferVar1 = infer ctx var1 in
      unify inferVar1 type1;
      type1





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
