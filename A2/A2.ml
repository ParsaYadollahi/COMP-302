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
        if cur_el = x then aux remainder (cur_el, cur_num+1) (max_el, max_num)
        else if cur_num > max_num then aux remainder (x, 1) (cur_el, cur_num)
        else aux remainder (x, 1) (max_el,max_num) in
  match List.sort compare l with
  | [] -> failwith "Empty list"
  | x::remainder ->
      aux remainder (x, 1) (x, 1)
;;


(* Question 1.2 : Most common consecutive pairing *)

let pair_mode_tests: (int list * (int * int) ) list = [
  ([1;2], (1,2));
  ([1;1;1;1;2;3], (1,1));
  ([1;3;4;5;1;3], (1,3));
  ([1;1;2;2;2;1;1], (1,1))
] ;;

let pair_mode (l: 'a list) : 'a * 'a =
  let rec pair (l: 'a list) : ('a * 'a) list = match l with
    | [] -> []
    | [_] -> []
    | [h1;h2] -> [(h1,h2)]
    | h1::h2::tail ->
        (h1,h2) :: (pair (h2:: tail) ) in
  match l with
  | [] -> failwith "Empty list"
  | [_] -> failwith "Needs more elements"
  | l ->
      mode (pair l) ;
;;


(* Section 2 : Custom data types *)

let convert_time ((from_unit, val_) : time_unit value) to_unit : time_unit value =
  if from_unit = Second && to_unit = Hour then (from_unit,val_/.3600.)
  else if from_unit = Hour && to_unit = Second then (from_unit, val_ *. 3600.)
  else (from_unit, val_)
;;

let convert_dist ((from_unit, val_) : dist_unit value) to_unit : dist_unit value =
  if from_unit = Foot && to_unit = Mile then (from_unit,val_ /. 5280.)
  else if from_unit = Foot && to_unit = Meter then (from_unit, val_ /. 3.28084)
  else if from_unit = Meter && to_unit = Mile then (from_unit, val_ /. 1609.344)
  else if from_unit = Meter && to_unit = Foot then (from_unit, val_ /. 0.3048)
  else if from_unit = Mile && to_unit = Foot then (from_unit, val_ *. 5280.)
  else if from_unit = Mile && to_unit = Meter then (from_unit, val_ *. 1609.344)
  else (from_unit, val_)
;;

let convert_speed ((from_unit, val_) : speed_unit value) to_unit : speed_unit value =
  let (from_unit_dist,_) = from_unit in
  let (_,from_unit_time) = from_unit in
  let (to_unit_dist,_) = to_unit in
  let (_,to_unit_time) = to_unit in
  let (dist_measure, dist) = convert_dist ((from_unit_dist), val_) (to_unit_dist) in
  let (time_measure, time) = convert_time (from_unit_time, 1.) to_unit_time in
  ((dist_measure, time_measure), dist/.time)
;;

let add_speed (a : speed_unit value) ((b_unit, b_val) : speed_unit value) : speed_unit value =
  let ((a_dist,_),_) = a in
  let ((_,a_time),_) = a in
  let ((_,_),a_speed) = a in
  let ((_, _), new_val) = convert_speed ((a_dist, a_time), a_speed) (b_unit) in
  ((a_dist, a_time), b_val +. new_val)
;;

let dist_traveled time ((speed_unit, speed_val) : speed_unit value) : dist_unit value =
  let (time_u, time) = time in
  let (speed_dist, _) = speed_unit in
  let ((new_dist, _), new_val) = convert_speed (speed_unit, speed_val) (speed_dist, time_u) in
  (new_dist, new_val *. time)

;;

(* Section 3 : recursive data types/induction *)
(* Question 3 *)

let t =
  Branch (10., [
      Branch (3., [Leaf; Leaf; Leaf]);
      Branch (1., [ Branch (3., [Leaf; Leaf; Leaf]); Leaf; Branch (4., [])]);
      Branch (4., []);
      Branch (4., []);
    ])

let t1 =
  Branch (5., [
      Branch (3., [Leaf; Leaf; Leaf]);
      Branch (4., []);
      Leaf;
    ])

let t2 =
  Branch (5., [
      Branch (3., [Leaf; Leaf; Leaf]);
      Leaf;
      Branch (4., [])
    ])

let t3 =
  Branch (5., [])

let t4 =
  Leaf

let t5 =
  Branch (5., [
      Branch (3., [Leaf; Leaf; Leaf]);
      Branch (6., []);
      Leaf;
    ])


let passes_da_vinci_tests : (tree * bool) list = [
  (t , false);
  (t1, true);
  (t2, true);
  (t3, true);
  (t4, true);
  (t5, false);
      ] ;;

let extract_content (branch) = match branch with
  | Leaf -> (0., [])
  | Branch (width, children) -> (width, children)
;;

let rec sum_of_squares (branch_widths : 'a list) (sum: 'a) = match branch_widths with
  | [] -> sum
  | x::remainder ->
      let new_sum = sum +. x**2. in
      sum_of_squares remainder new_sum

let rec traverse_children (tree_list : tree list) (width_list : float list) = match tree_list with
  | [] ->
      sum_of_squares width_list 0.
  | x::remainder ->
      if x = Leaf then traverse_children remainder width_list
      else let (width,_) = extract_content x in
        let new_list = width_list @ [width] in
        traverse_children remainder new_list
;;

let rec passes_da_vinci_2 t valid =
  let rec helper l valid = match l with
    | [] -> valid
    | x::xs ->
          let y = passes_da_vinci_2 x valid in
          helper xs y in

  match t with
  | Leaf -> valid
  | Branch (width, children) ->
      let children_width = traverse_children children [] in
      let y = width ** 2. >= children_width in
      if valid then
        helper children y
      else helper children false;
;;

let passes_da_vinci t = match t with
  | Leaf -> true
  | Branch (_,_ ) -> passes_da_vinci_2 t true ;;
