open List
(* open Sets *)

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  List.sort_uniq Stdlib.compare (if Option.is_none s || List.mem (Option.get s) nfa.sigma then
    List.fold_left (fun a x -> 
      match x with (b, c, d) -> 
        if List.mem b qs then
        if c = s then
           d :: a
          else a
        else a

      ) [] nfa.delta
  else [])

let rec e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  let one_iteration_eclosure = List.sort_uniq Stdlib.compare (
  List.fold_left (fun a x -> 
    match x with (b, c, d) ->
      if Option.is_none c then
        if List.mem b qs then d :: a
        else a
      else a
    ) qs nfa.delta )in
    let new_eclosure = one_iteration_eclosure in
    if new_eclosure = qs then qs else e_closure nfa new_eclosure
    

let rec accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let char_lst = explode s in
  let rec acc cs cl = match cl with
  [] -> List.fold_left (fun a x -> 
    if List.mem x nfa.fs then true else a) false (e_closure nfa cs)
  |h::t -> acc (move nfa (e_closure nfa cs) (Some h)) t in
  acc (e_closure nfa [nfa.q0]) char_lst

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  List.sort_uniq Stdlib.compare (List.fold_left (fun a x ->
    (e_closure nfa (move nfa qs (Some x)))::a
  ) [] nfa.sigma)

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  List.sort_uniq Stdlib.compare (List.fold_left (fun a x ->
      (qs, Some x, e_closure nfa (move nfa qs (Some x)))::a
      ) [] nfa.sigma)

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  if (List.fold_left (fun a x ->
    if List.mem x nfa.fs then true else a
    ) false qs) then [qs] else []

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
  failwith "unimplemented"
  

let rec nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  let starting_state = e_closure nfa [nfa.q0] in
  let n_states ps = (match (
      List.sort_uniq Stdlib.compare (List.fold_left (fun a x -> 
       (new_states nfa x)@a
     ) ps ps)) with h::t -> t | [] -> []) in
  let rec all_states ns = 
    if ns = (n_states ns) then ns else all_states (n_states ns) in
  let states = List.sort_uniq Stdlib.compare (starting_state::(all_states (List.fold_left ( fun a x ->
    [x]::a
  ) [] nfa.qs))) in 
  let transitions = List.fold_left (
    fun a x -> 
      match x with (b,c,d) -> if d = [] then a else x::a
  ) [] (List.fold_left (fun a x -> 
    (new_trans nfa x)@a
    ) [] states)
  in
  {
      qs = states;
      sigma = nfa.sigma;
      delta = transitions;
      q0 = starting_state;
      fs = (
        List.fold_left (fun a x -> 
          match new_finals nfa x with
          [] -> a
          |_ -> x::a 
      ) [] states
      ) 
    }