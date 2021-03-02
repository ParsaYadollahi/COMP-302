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
  let verify input =
    if input = !ref_master then counter := !counter + 1
    else raise WrongPassword; failed := !failed + 1
  in
  let save m a p =
    if !failed < 3 then (verify m; ref_list := (a, encrypt m p) :: !ref_list)
    else raise AccountLocked
  in
  let get_force m a = find_map
    (
      fun x -> match x with
      | (y,z) ->
        if a = y
        then Some(decrypt m z)
        else None
    ) !ref_list in
  let get m a =
    if !failed < 3 then (
      verify m; get_force m a
    )
    else raise AccountLocked
  in
  let update_master m1 m2 = verify m1;
  List.map (
    fun x -> match x with
      | (_,z) -> encrypt m2 (decrypt m1 z)
    ) !ref_list;
    ref_master := m2
  in
  let count_ops m =
    if !failed < 3 then (verify m; !counter)
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
