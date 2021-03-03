(* Question 1 *)

let rec find_map (f : 'a -> 'b option) (l : 'a list) : 'b option =
  match l with
  | [] -> None
  | x::xs ->
      match f x with
      | None -> find_map f xs
      | Some x -> Some x
;;

let par x = (x / 2) = 0 ;;
let lst = [1;2;3;4;5;6;7;8;9]

let partition (p : 'a -> bool) (l : 'a list) : ('a list * 'a list) =
  let helper = fun el (tr, fa) ->
    if p el
    then el :: tr, fa
    else
      tr, el :: fa
  in List.fold_right helper l([],[])
;;

(* Question 2 *)

let make_manager (masterpass : masterpass) : pass_manager =
  let ref_list : (address * password) list ref = ref [] in
  let counter = ref 0 in
  let failed_counter = ref 0 in
  let ref_master = ref masterpass in
  let verify_pass masterpass_input  =
    if masterpass_input = !ref_master then
      counter := !counter + 1
    else
      (
        if !failed_counter > 2 then
          raise AccountLocked
        else
          raise WrongPassword;
        failed_counter := !failed_counter + 1
      )
  in
  let save master address password_in =
    if !failed_counter >= 3 then
      raise AccountLocked
    else
      (
        verify_pass master;
        ref_list := (address, encrypt master password_in) :: !ref_list
      )
  in
  let get_force master address =
    let f = fun output ->
      let (a, p) =
        output in
      if address = a then
        Some (decrypt master p) else
        None in
    find_map f !ref_list in
  let get master address =
    if !failed_counter >= 3 then
      raise AccountLocked
    else
      (
        verify_pass master;
        get_force master address
      )
  in
  let update_master p1 p2 =
    verify_pass p1;
    List.map (
      fun output ->
        let (a,p) = output in
        encrypt p2 (decrypt p1 p)
    ) !ref_list;
    ref_master := p2
  in
  let count_ops master =
    if !failed_counter >= 3 then
      raise AccountLocked
    else
      (
        verify_pass master;
        !counter
      )
  in {save; get_force; get; update_master; count_ops}
;;

(* Question 3 *)

(* Counting values at same time *)
let catalan_count (n : int) : (int * int) =
  let count_rec_calls = ref 0 in
  let rec catalan n =
    count_rec_calls := !count_rec_calls + 1;
    if n != 0 then
      (
        let rec helper i n acc =
          if i <= n then
            helper (i + 1) n (catalan i * catalan (n - i) + acc)
          else
            acc
        in
        helper 0 (n-1) 0
      )
    else 1 in
  if n != 0 then
    let output = catalan n in
    (output, !count_rec_calls)
  else
    (1, 1)
;;

(* Memoization function *)
let memoize (f : ('a -> 'b) -> 'a -> 'b) (stats : stats) : 'a -> 'b =
  let hash = Hashtbl.create 1000 in
  let rec f' x =
    match Hashtbl.find_opt hash x with
    | None ->
        let elemeent = f f' x in
        stats.entries := !(stats.entries) + 1;
        Hashtbl.add hash x elemeent;
        let Some new_entry = Hashtbl.find_opt hash x in
        new_entry
    | Some entry ->
        stats.lkp := !(stats.lkp) + 1;
        entry
  in
  f'
;;

(* Version of catalan that can be memoized *)
let memo_cat (recf : int -> int) (n : int) : int =
  if n != 0 then
    (
      let rec helper i n acc =
        if i <= n then
          helper (i + 1) n (recf i * recf (n - i) + acc)
        else
          acc
      in
      helper 0 (n - 1) 0
    )
  else 1
;;

let catalan_m (n : int) : int * stats =
  let stats = {
    lkp = ref 0;
    entries = ref 0;
  } in
  let catalan_no = memoize memo_cat stats n in
  (catalan_no, stats)
;;
