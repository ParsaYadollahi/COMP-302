(* Question 1 *)

let rec find_map (f : 'a -> 'b option) (l : 'a list) : 'b option =
  match l with
  | [] -> None
  | x::xs ->
      match f x with
      | Some x -> Some x
      | None -> find_map f xs
;;

let par x = if x/2 = 0 then true else false ;;
let lst = [1;2;3;4;5;6;7;8;9]

let partition (p : 'a -> bool) (l : 'a list) : ('a list * 'a list) =
  raise NotImplemented
  (* let tru = [] in
  let flse = [] in
  List.fold_right (fun x a -> match x with
  | [] -> (tru, flse)
  | x ->
    if p x then ((tru::x), flse) else (tru, (flse::x)) ) l (tru, flse) *)
;;

(* Question 2 *)

let make_manager (masterpass : masterpass) : pass_manager =
  let ref_list : (address * password) list ref = ref [] in
  let ref_master = ref masterpass in
  let counter = ref 0 in
  let failed = ref 0 in
  let verify_pass masterpass_input =
    if masterpass_input = !ref_master then counter := !counter + 1
    else (
      if !failed > 2 then raise AccountLocked
      else raise WrongPassword; failed := !failed + 1
    )
  in
  let save master address password_in =
    if !failed < 3 then (verify_pass master; ref_list := (address, encrypt master password_in) :: !ref_list)
    else raise AccountLocked
  in
  let get_force master address =
    let f = fun tuple -> let (add, pass) = tuple in if address = add then
    Some (decrypt master pass) else
    None in
    find_map f !ref_list in
  let get master address =
    if !failed < 3 then (
      verify_pass master;
      get_force master address
    )
    else raise AccountLocked
  in
  let update_master m1 m2 = verify_pass m1;
  List.map (
    fun x -> match x with
      | (_,z) -> encrypt m2 (decrypt m1 z)
    ) !ref_list;
    ref_master := m2
  in
  let count_ops master =
    if !failed < 3 then (verify_pass master; !counter)
    else raise AccountLocked
  in {save; get_force; get; update_master; count_ops}
;;

(* Question 3 *)

(* Counting values at same time *)
let catalan_count (n : int) : (int * int) =
  let count_rec_calls = ref 0 in
  raise NotImplemented
;;

(* Memoization function *)
let memoize (f : ('a -> 'b) -> 'a -> 'b) (stats : stats) : 'a -> 'b =
  let hash = Hashtbl.create 1000 in
  let rec f' x =
    raise NotImplemented
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
