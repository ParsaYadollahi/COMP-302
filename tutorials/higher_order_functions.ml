let identity x = x ;;
let id = identity ;;

let square_int : int -> int = fun x -> x * x ;;

let rec basic_sum (a,b) =
  if a > b then 0 else a+basic_sum(a+1, b);;

basic_sum (3,6);;


let rec square_sum (a,b) =
  if a > b then 0 else (a*a) + square_sum(a+1, b);;

square_sum (1,5);;

let rec sum on_num (a,b) =
  if a > b then 0 else on_num a + sum on_num (a+1,b) ;;

sum id (3 ,6) ;;

let square_sum = sum square_int ;;
(* ^ Same as : let square_sum (a, b) = sum square_int (a, b);; *)


(* CAN ABSTRACT NOW *)
let rec non_consec_sum on_num stop next curr =
  if stop curr then 0
  else on_num curr + non_consec_sum on_num stop next (next curr)
;;


let odd_sum on_num (a, b) =
  if a mod 2 = 1
  then non_consec_sum on_num (fun curr -> b < curr) (fun curr -> 2 + curr) a
  else non_consec_sum on_num ((>) b) ((+) 2) (a + 1)
;;

odd_sum square_int (2,5) ;;
(* note:
2 < 4 = (<) 2 4
so ==>  fun curr -> b < curr == (>) b
*)



let sum_over_lists on_el l =
  non_consec_sum
    (* (fun (h :: t) -> on_el h) *)
    (fun l -> on_el (List.hd l))
    ((=) [])
    List.tl
    l
;;


sum_over_lists List.length [[1;2]; [3;4;5]; []; [1]] ;;
sum_over_lists square_int [5;2;3;1] ;;


let rec series comb on_el stop next acc curr =
  if stop curr
  then acc
  else
    let add = on_el curr in
    let acc' = comb acc add in
    (* Comb is built in *)
    let curr' = next curr in
    series comb on_el stop next acc' curr'
;;

let intsum (f: int -> int) ((start:int), (step:int), (stop: int)) =
  let stop curr =
    if step < 0 then curr < stop
    else curr > stop
  in
  series (+) f stop ((+) step) 0 start
;;

let triangle n = intsum id (1, 1, n);;
intsum square_int (7, -2, 1) ;;


let floatincrsum f (start, step, stop) =
  series (+.) f (fun curr -> curr > stop) ((+.) step) 0. start
;;

let integral f (lo, hi) dx =
  dx *. floatincrsum f (lo +. dx /. 2., dx, hi)
;;



(* Existing common high order function and implementions *)
(* init: int -> (int -> 'a) -> 'a list *)
(* list_init 2 f  = [f 0; f 1] *)
let rec list_init (len: int) (f: int -> 'a) : 'a list =
  if len < 0 then failwith "can't make a list of negative length"
  else if len = 0 then []
  else (list_init (len-1) f) @ [f (len - 1)]
;;

(* The function above is a quadratic-time algo -> building it from left to right *)


(* find_opt: ('a -> bool) -> 'a list -> 'a option  *)
(* the same as let rec listfindopt p l - match l with | | | ... *)
let rec listfindopt p = function
  | [] -> None
  | h :: t ->
      if p h then (Some h) (** Some because we need the same type as None *)
      else listfindopt p t
;;

let listinitcg len =
  let rec init curr =
    if curr = len then (fun f -> [])
    else let tail = init (curr + 1) in
      fun f -> (f curr) :: (tail f)
  in
  init 0
;;
