(* Question 1 *)

let solve_maze (maze : MazeGen.maze) : MazeGen.dir list =
  raise NotImplemented
;;

(* You can run this code to manually test your solutions. *)
let test_maze width height =
  let maze = MazeGen.random width height in
  let path = solve_maze maze in
  print_string (MazeGen.string_of_maze ~path maze)
;;

(* Question 2 *)

module Range : RangeSig = struct
  open Seq

  let rec zip (seq1 : 'a seq) (seq2 : 'b seq) : ('a * 'b) seq =
  let seqs = (seq1()), (seq2()) in
    match seqs with
    | Cons(x, x'), Cons (y, y') ->
      fun() ->
        let zipXY = zip x' y' in
        Cons ((x,y), zipXY)
    | Nil, _ | _, Nil -> fun() -> Nil

  let rec keep_until (p : 'a -> bool) (seq : 'a seq) : 'a seq =
      match seq() with
      | Nil ->
        fun () -> Nil
      | Cons (a, b) ->
        if p a then (
          fun () -> Nil
        ) else (
          fun() ->
            Cons(a, keep_until p b)
        )

  let to_list (seq : 'a seq) : 'a list =
    let rec aux s = match s() with
      | Nil -> []
      | Cons(x,y) -> x :: aux y
    in
    aux seq

  exception Invalid_argument

  let range (start : int) (step : int) (stop : int) : int seq =
  if (step > 0 && (start > stop)) then
    raise Invalid_argument
  else
    let test_ftn a =
      if start < stop then (
        a >= stop
      ) else (
        a <= stop
      ) in
    keep_until test_ftn ((map (fun b -> b + start)) (map (fun b -> b * step) nats))

end ;;

(* This function is just another example of the use of optional arguments.
  Removing or altering it should not change your grade, as the function Range.range
  is being tested. Our grader cannot, at the moment, handle optional arguments.
*)
let range ?(start : int = 0) ?(step : int = 1) (stop : int) : int seq =
  Range.range start step stop
;;

(* Examples of uses of optional arguments, lazy-evaluated *)
let example_ranges () = [
  range 10;
  range ~start:5 10;
  range ~step:2 20;
  range ~start:100 ~step:(~-2) 50
] ;;

(* Question 3 *)

module RationalField : (AlgField with type t = rational) = struct
  type t = rational

  let equal a b = a.den = 0 && b.den = 0 && a.den * b.num = a.num * b.den
  let zero = {
    den = 1;
    num = 0;
  }
  let one = {
    den = 1;
    num = 1;
  }
  let add x y = {
    den = (
      x.den*y.den
    );
    num = (
      x.num * y.den
    ) + (
      y.num * x.den
    );
  }
  let inv x = {
    den = (x.num);
    num = x.den;
  }
  let neg x = {
    den = (x.den);
    num = x.num * (-1);
  }
  let mul x y = {
    den = (
      x.den * y.den
    );
    num = (
      x.num * y.num
    );
  }

end ;;
(*
module BooleanField : (AlgField with type t = bool) = struct
  type t = bool

  let equal = (=)
end ;;

module EllipticCurves (F : AlgField) : sig
  type point = F.t * F.t
  val easyECs : bool
  val onCurve : F.t -> F.t -> point -> bool
end = struct
  type point = F.t * F.t
(* Implement easyECs and onCurve function below *)

end

(* Elliptic curve definitions using functor *)
(* Do not remove these modules from your code: we need it for testing. *)
module Rational_EC = EllipticCurves(RationalField)
module Boolean_EC = EllipticCurves(BooleanField)
module Float_EC = EllipticCurves(FloatField)
(* *)
As mentioned in prelude, you can test this in the Toplevel, just do not place it
in your code below, or the grader will have a fit.
                                                It has to do with weird dependencies in the grader. It's sad.

module Complex_EC = EllipticCurves(ComplexField) *)
