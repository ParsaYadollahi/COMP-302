(* Question 1 *)

let rec find_map (f : 'a -> 'b option) (l : 'a list) : 'b option =
  match l with
  | [] -> None
  | x::xs ->
      match f x with
      | Some x -> Some x
      | None -> find_map f xs
;;

let par x = (x / 2) = 0 ;;
let lst = [1;2;3;4;5;6;7;8;9]

let partition (p : 'a -> bool) (l : 'a list) : ('a list * 'a list) =
  let helper = fun (e) ((t, f)) ->
    if p e
    then e:: t, f
    else
      t, e :: f
  in List.fold_right helper l([],[])
;;

(* Question 2 *)

let make_manager (masterpass : masterpass) : pass_manager =
  let ref_list : (address * password) list ref = ref [] in
  let ref_master = ref masterpass in
  let counter = ref 0 in
  let failed_counter = ref 0 in
  let verify_pass masterpass_input masterpass_og =
    if masterpass_input = !masterpass_og then counter := !counter + 1
    else (
      if !failed_counter > 2 then raise AccountLocked
      else raise WrongPassword; failed_counter := !failed_counter + 1
    )
  in
  let save master address password_in =
    if !failed_counter < 3 then (verify_pass master ref_master; ref_list := (address, encrypt master password_in) :: !ref_list)
    else raise AccountLocked
  in
  let get_force master address =
    let f = fun tuple -> let (add, pass) = tuple in
      if address = add then
        Some (decrypt master pass) else
        None in
    find_map f !ref_list in
  let get master address =
    if !failed_counter < 3 then (
      verify_pass master ref_master;
      get_force master address
    )
    else raise AccountLocked
  in
  let update_master curr_pass new_pass = verify_pass curr_pass ref_master;
    List.map (
      fun tuple -> let (add,pass) = tuple  in
        encrypt new_pass (decrypt curr_pass pass)
    ) !ref_list;
    ref_master := new_pass
  in
  let count_ops master =
    if !failed_counter < 3 then (verify_pass master ref_master; !counter)
    else raise AccountLocked
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
          helper (i + 1) n (acc + catalan i * catalan (n - i))
        else
          acc
        in
        helper 0 (n-1) 0
      )
      else 1 in
  if n = 0 then
    (1, 1)
  else
    let output = catalan n in
    (output, !count_rec_calls)
;;

(* Memoization function *)
let memoize (f : ('a -> 'b) -> 'a -> 'b) (stats : stats) : 'a -> 'b =
  let hash = Hashtbl.create 1000 in
  let rec f' x =
    match Hashtbl.find_opt hash x with
    | None -> let elemeent = f f' x in
        stats.entries := !(stats.entries) + 1;
        Hashtbl.add hash x elemeent;
        let Some new_entry = Hashtbl.find_opt hash x in
        new_entry
    | Some entry -> stats.lkp := !(stats.lkp) + 1;
        entry
  in
  f'
;;

(* Version of catalan that can be memoized *)
let memo_cat (recf : int -> int) (n : int) : int =
  raise NotImplemented
;;

let catalan_m (n : int) : int * stats =
  raise NotImplemented
;;
