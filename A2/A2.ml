(* Section 1 : Lists *)

(* Question 1.1 : Most common element of *sorted* list *)

let mode_tests: (int list * int) list = [
  ([1], 1);
  ([1;2;2], 2);
  ([1;1;2;2;1;2;1;2], 1);
  (* ([(1,1);(1,2);(1,2)], (1,2)) *)
] ;;

let mode (l: 'a list) : 'a =
  let rec aux (l : 'a list) ((cur_el, cur_num) : 'a * int) ((max_el, max_num) : 'a * int) =
    match l with
    | [] ->
      if cur_num > max_num then cur_el else max_el
    | x :: remainder ->
        (* Printf.printf "cur_num = %d\n" cur_num; *)
        if cur_el = x then aux remainder (cur_el, cur_num+1) (max_el, max_num)
        else if cur_num > max_num then aux remainder (x, 1) (cur_el, cur_num)
        else aux remainder (x, 1) (max_el,max_num) in
  match List.sort compare l with
  | [] -> failwith "Empty list"
  | x::remainder ->
  (* List.iter (Printf.printf "%d ") remainder; *)
      aux remainder (x, 1) (x, 1)
;;


(* Question 1.2 : Most common consecutive pairing *)

let pair_mode_tests: (int list * (int * int) ) list = [
  ([1;1;2;2;2;1;1], (2,3))
] ;;

let pair_mode (l: 'a list) : 'a * 'a =
  let rec pair (l: 'a list) : ('a * 'a) list = match l with
  | [h1;h2] -> [(h1,h2)]
  | h1::h2::tail ->
    (h1,h2) :: (pair (h2:: tail) ) in
  match l with
  | [] -> failwith "Empty list"
  | [x] -> failwith "Needs more elements"
  | l ->
    mode (pair l) ;
;;


(* Section 2 : Custom data types *)

let convert_time ((from_unit, val_) : time_unit value) to_unit : time_unit value =
  notimplemented ()
;;

let convert_dist ((from_unit, val_) : dist_unit value) to_unit : dist_unit value =
  notimplemented ()
;;

let convert_speed ((from_unit, val_) : speed_unit value) to_unit : speed_unit value =
  notimplemented ()
;;

let add_speed (a : speed_unit value) ((b_unit, b_val) : speed_unit value) : speed_unit value =
  notimplemented ()
;;

let dist_traveled time ((speed_unit, speed_val) : speed_unit value) : dist_unit value =
  notimplemented ()
;;

(* Section 3 : recursive data types/induction *)

let passes_da_vinci_tests : (tree * bool) list = [] ;;

let rec passes_da_vinci t =
  notimplemented ()
;;
