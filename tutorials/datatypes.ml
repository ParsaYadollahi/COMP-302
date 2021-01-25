type myUnit = MyUnit;;

let v = MyUnit ;;

let v = () ;;

type myBool = MyTrue | MyFalse ;;

let toMyBool (b: bool) = if b then MyTrue else MyFalse ;;

let toMyBool (b: bool) = match b with
  | true -> MyTrue
;; (* Patter matching error *)

let toMyBool (b: bool) = match b with
  | true -> MyTrue
  | false -> MyFalse
;; (* Patter matching error *)


let myLogicAnd a b = match (a,b) with
 | MyTrue, MyTrue -> MyTrue
 | MyTrue, MyFalse -> MyFalse
 | MyFalse, _ -> MyFalse (* no matter what the second arg, if false go to this one *)
 ;;

let myLogicAnd a b = match (a,b) with
 | MyTrue, b -> b
 | MyFalse, _ -> MyFalse
 ;;

let myLogicAnd a b = match (a,b) with
 | MyTrue,MyTrue -> MyTrue
 | _ -> MyFalse
 ;;

(* -------------- *)
type dist_unit = Feet | Meter | Mile ;;
type time_unit = Second | Hour ;;
type speed_unit = dist_unit * time_unit ;;

type coord = Coordinate of float * float ;;

let c1 = Coordinate(2.5, 3.6) ;;
(* let c1 = Coordinate ==> Error ;; *)

(* -------------- *)
type 'anyType option = None | Some of 'anyType ;;
(** name is option - type is optioncould have written 'a  - think the apost returns anytype *)

type opt_int = int option

let add_int_opt (a: opt_int) (b: opt_int) =
  match (a,b) with
  | Some v1, Some v2 -> Some(v1 + v2)
  | _ -> None
  ;;

let v = Some 1 ;;
let v2 = Some 1. ;;
let v3 = None ;; (* comes out as 'a optoin *)

type 'a value = IntVal of 'a * int | FloatVal of 'a * float ;; (** IntVal ("AAA", 5) - generic value type*)

let extract_content (v: 'a value) = match v with
 | IntVal (content, integer) -> content
 | FloatVal (content, floatnum) -> content
 ;;

let value_to_float v = match v with
| IntVal (_, integer) -> float_of_int integer
| FloatVal (_, floatnum) -> floatnum
;;

let v = IntVal("Abc" , 4);;

let speed_value : speed_unit value = FloatVal ((Feet, Second), 2.5) ;;

type speed_transform = speed_unit value -> speed_unit value -> speed_unit value ;;

type make_float_into_ints = float -> int ;; (** takes floats and returns ints *)
let fn : make_float_into_ints = function x -> int_of_float x ;;
let fn2 : make_float_into_ints = function x -> int_of_float x * 2 ;;


(** Recursive types *)

type nat = Zero | Succ of nat ;;
Zero ;;
let one = Succ Zero ;;
let two = Succ (Succ Zero) ;;
(* let two = Succ one = val two : nat = Succ (Succ Zero) *)

type crazyType = Crazy of crazyType ;; (** Will compile *)
(* let v : crazyType = Crazy (Crazy (...)) --> to infinite *)


type 'a myList =
  Empty | Comb of 'a * 'a myList ;;
  (** ^ = Either empty or combination of a list and another list *)

let short_int_list = Comb (1, Comb (2, Empty));;
let short_float_list = Comb (3., Empty);;


(* Trees - example cake *)
type 'a cake = Slice of 'a | Cake of 'a cake * 'a cake;;

type ingredients = Cherry | Chocolate | Lemon | Strawberry ;;

let choc_cake = Slice Chocolate ;; (** One cake *)
let choc_cake2 = Cake (Slice Chocolate, choc_cake);; (** two cakes *)

let rec count c = match c with
  | Slice _ -> 1
  | Cake (c1, c2) -> count c1 + count c2 ;;
