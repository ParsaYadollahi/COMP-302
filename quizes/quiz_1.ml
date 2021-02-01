let zip l1 l2 =
  let rec zip' (l1, l2) = match l1, l2 with
    | [], [] -> []
    | x::xs, y::ys -> (x,y)::zip' l1 l2
  in
  if length l1 = length l2 then
    zip' (l1, l2)
  else raise Error ;;

let point = (3, 4)
let component_x (x,y) = x
let component_y (x,y) = y

let shift_point n =
  (component_x point + n , component_y point + n)
let point = shift_point 1


let rec rev1 lst =
    match lst with
    | [] -> []
    | x :: xs -> (rev1 xs) @ [x]



let rev2 lst =
    let rec go lst acc =
        match lst with
        | [] -> acc
        | x :: xs -> go xs (x::acc)
        in
    go lst []


let x = 1 in
  let plus_x n = n + x in
    let x = 2 in
      plus_x x ;;

let rec triangle n =
  if n = 1 then 1
  else n + triangle (n-1)


let prod l =
  let rec product l acc = match l with
    | [] -> 1.
    | x::xs ->
    product xs acc *. x
    in
    (product l 1.)

let rec partial_sums l = match l with
  | [] -> []
  | [x] -> [x]
  | x::y::ys -> x :: (partial_sums ((x + y):: ys));;
