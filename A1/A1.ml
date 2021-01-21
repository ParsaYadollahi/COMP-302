(* Reminder: Do not modify the function signature. Make a backup of your code regularly. Do not define external helper functions, unless the exercise explictly tells you to do so. *)

(*
    Section 1 : Fix Me

    First, correct and add test cases by adding elements to `distance_tests`, `hanoi_tests` and `fact_tests`.
    Then, correct the implementation of functions `distance`, `hanoi` and `fact`.
*)

(* Question 1.1 : Lattice 2D Euclidean distance *)

let distance_tests = [
  ( ((0, 0), (0, 0)), (0.) );
  ( ((0, 0), (3, 4)), (5.) );
  ( ((0, 0), (1, 1)), (1.41421356237309515) );
]
;;

let  distance ((x1, y1): (int * int)) ((x2, y2): (int * int)) : float =
  let dx = (x1 - x2) in
  let dy = (y1 - y2) in
  sqrt (float_of_int(dx * dx + dy * dy))
;;


(* Question 1.2 : Tower of Hanoi recursive definition *)

let hanoi_tests = [
  (1, 1);
  (2, 3);
  (3,7);
]
;;

let rec hanoi (n: int) : int =
  if n <= 0 then domain ()
  else
  if n <= 1 then 1 else
    2 * hanoi(n-1) + 1
;;


(* Question 1.3 : non-tail-recursive factorial *)

let fact_tests = [
  (0, 1.);
  (1, 1.);
  (2, 2.);
  (3, 6.)
]
;;

let rec fact (n: int): float =
  if n < int_of_float(1.) then 1. else
    fact (int_of_float(float_of_int(n) -. 1.)) *. float_of_int(n)
;;


(*
    Section 2: Hailstone sequence
Add tests to `collatz_tests` and implement both `collatz_helper` and `collatz`.
                                                                               *)

let collatz_tests = [
  (1,0);
  (2,1);
  (3, 7);
  (4, 2);
  (5, 5);
  (6, 8);
  (7, 16);
  (15, 17);
]
;;

let rec collatz_helper (n: int) (steps_so_far: int) : int =
  if n = 1 then steps_so_far
  else
  if n mod 2 = 0 then
    collatz_helper (n/2) (steps_so_far+1)
  else
    collatz_helper (3 * n + 1) (steps_so_far+1)
;;

let collatz (n: int) : int =
  collatz_helper n 0
;;


(*
    Section 3: Riemann Zeta function
    Implement the `approx_zeta` function.
    You do not need to modify any other parts inside the `zeta` function
*)

let zeta_tests = [
  (3., 1.20205690314079017);
  (4., 1.08232323371051709);
  (5., 1.03692775514329338);
]
;;

let zeta (k: float) : float =
  let rec approx_zeta k acc n sum_so_far =
    if (n ** -.k) < acc then sum_so_far
    else
      approx_zeta k acc (n +. 1.) (sum_so_far +. (n ** -.k ))
  in
    (*  Note that we put < 2. while the function still works
        to evaluate any smaller arguments
  *)
  if k < 2.
  then domain ()
  else approx_zeta k epsilon_float 1. 0.
;;
