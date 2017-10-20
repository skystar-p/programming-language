(*
 * SNU 4190.310 Programming Languages 2017 Fall
 *  K- Interpreter Skeleton Code
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)

(* Location Signature *)
module type LOC =
sig
  type t
  val base : t
  val equal : t -> t -> bool
  val diff : t -> t -> int
  val increase : t -> int -> t
end

module Loc : LOC =
struct
  type t = Location of int
  let base = Location(0)
  let equal (Location(a)) (Location(b)) = (a = b)
  let diff (Location(a)) (Location(b)) = a - b
  let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM =
sig
  type 'a t
  exception Not_allocated
  exception Not_initialized
  val empty : 'a t (* get empty memory *)
  val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
  val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
  val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
  type ('a, 'b) t
  exception Not_bound
  val empty : ('a, 'b) t (* get empty environment *)
  val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
  val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
  exception Not_allocated
  exception Not_initialized
  type 'a content = V of 'a | U
  type 'a t = M of Loc.t * 'a content list
  let empty = M (Loc.base,[])

  let rec replace_nth = fun l n c ->
    match l with
    | h::t -> if n = 1 then c :: t else h :: (replace_nth t (n - 1) c)
    | [] -> raise Not_allocated

  let load (M (boundary,storage)) loc =
    match (List.nth storage ((Loc.diff boundary loc) - 1)) with
    | V v -> v
    | U -> raise Not_initialized

  let store (M (boundary,storage)) loc content =
    M (boundary, replace_nth storage (Loc.diff boundary loc) (V content))

  let alloc (M (boundary,storage)) =
    (boundary, M (Loc.increase boundary 1, U :: storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
  exception Not_bound
  type ('a, 'b) t = E of ('a -> 'b)
  let empty = E (fun x -> raise Not_bound)
  let lookup (E (env)) id = env id
  let bind (E (env)) id loc = E (fun x -> if x = id then loc else env x)
end

(*
 * K- Interpreter
 *)
module type KMINUS =
sig
  exception Error of string
  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp

  type program = exp
  type memory
  type env
  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
  val emptyMemory : memory
  val emptyEnv : env
  val run : memory * env * program -> value
end

module K : KMINUS =
struct
  exception Error of string

  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp

  type program = exp

  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)

  type memory = value Mem.t
  type env = (id, env_entry) Env.t
  and  env_entry = Addr of Loc.t | Proc of id list * exp * env

  let emptyMemory = Mem.empty
  let emptyEnv = Env.empty

  let value_int v =
    match v with
    | Num n -> n
    | _ -> raise (Error "TypeError : not int")

  let value_bool v =
    match v with
    | Bool b -> b
    | _ -> raise (Error "TypeError : not bool")

  let value_unit v =
    match v with
    | Unit -> ()
    | _ -> raise (Error "TypeError : not unit")

  let value_record v =
    match v with
    | Record r -> r
    | _ -> raise (Error "TypeError : not record")

  let lookup_env_loc e x =
    try
      (match Env.lookup e x with
      | Addr l -> l
      | Proc _ -> raise (Error "TypeError : not addr"))
    with Env.Not_bound -> raise (Error "Unbound")

  let lookup_env_proc e f =
    try
      (match Env.lookup e f with
      | Addr _ -> raise (Error "TypeError : not proc")
      | Proc (id_list, exp, env) -> (id_list, exp, env))
    with Env.Not_bound -> raise (Error "Unbound")

  let rec eval mem env e =
    match e with
    | READ x ->
      let v = Num (read_int()) in
      let l = lookup_env_loc env x in
      (v, Mem.store mem l v)
    | WRITE e ->
      let (v, mem') = eval mem env e in
      let n = value_int v in
      let _ = print_endline (string_of_int n) in
      (v, mem')
    | LETV (x, e1, e2) ->
      let (v, mem') = eval mem env e1 in
      let (l, mem'') = Mem.alloc mem' in
      eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2
    | LETF (x, l, e1, e2) ->
        eval mem (Env.bind env x (Proc (l, e1, env))) e2
    | ASSIGN (x, e) ->
      let (v, mem') = eval mem env e in
      let l = lookup_env_loc env x in
      (v, Mem.store mem' l v)
    | TRUE ->
        (Bool true, mem)
    | FALSE ->
        (Bool false, mem)
    | UNIT ->
        (Unit, mem)
    | NUM n ->
        (Num n, mem)
    | VAR id ->
        let l = lookup_env_loc env id in
        (Mem.load (mem) l, mem)
    | ADD (e1, e2) ->
        let ev1, mem1 = eval mem env e1 in
        let ev2, mem2 = eval mem1 env e2 in
        (Num ((value_int ev1) + (value_int ev2)), mem2)
    | SUB (e1, e2) ->
        let ev1, mem1 = eval mem env e1 in
        let ev2, mem2 = eval mem1 env e2 in
        (Num ((value_int ev1) - (value_int ev2)), mem2)
    | MUL (e1, e2) ->
        let ev1, mem1 = eval mem env e1 in
        let ev2, mem2 = eval mem1 env e2 in
        (Num ((value_int ev1) * (value_int ev2)), mem2)
    | DIV (e1, e2) ->
        let ev1, mem1 = eval mem env e1 in
        let ev2, mem2 = eval mem1 env e2 in
        (Num ((value_int ev1) / (value_int ev2)), mem2)
    | EQUAL (e1, e2) ->
        let ev1, mem1 = eval mem env e1 in
        let ev2, mem2 = eval mem1 env e2 in
        let res = (
          match ev1, ev2 with
          | Num a, Num b -> a = b
          | Bool a, Bool b -> a = b
          | Unit, Unit -> true
          | _, _ -> false ) in
        (Bool res, mem2)
    | LESS (e1, e2) ->
        let ev1, mem1 = eval mem env e1 in
        let ev2, mem2 = eval mem1 env e2 in
        (Bool ((value_int ev1) < (value_int ev2)), mem2)
    | NOT e ->
        let ev, mem' = eval mem env e in
        (Bool (not (value_bool ev)), mem')
    | SEQ (e1, e2) ->
        let ev1, mem1 = eval mem env e1 in
        let ev2, mem2 = eval mem1 env e2 in
        let res = (
          match ev1, ev2 with
          | _, a -> a ) in
        (res, mem2)
    | IF (e1, e2, e3) ->
        let e1', mem1 = eval mem env e1 in
        let ev1 = value_bool e1' in
        if ev1 then
          eval mem1 env e2
        else
          eval mem1 env e3
    | WHILE (e1, e2) ->
        let ev1, mem' = eval mem env e1 in
        if value_bool ev1 then
          let ev2, mem'' = eval mem' env e2 in
          eval mem'' env (WHILE (e1, e2))
        else
          (Unit, mem')
    | CALLV (id, el) ->
        let id_list, fexp, fenv = lookup_env_proc env id in
        let rec get_list cmem l evl =
          ( match l with
          | x::xs ->
              let ev, mem' = eval cmem env x in
              get_list mem' xs (ev::evl)
          | [] -> (evl, cmem) ) in
        let rel, mem' = get_list mem el [] in
        let fel = List.rev rel in
        let rec preapply l ll cenv cmem =
          match l, ll with
          | x::xs, y::ys ->
              let (r, mem'') = Mem.alloc cmem in
              let newmem = Mem.store mem'' r y in
              let newenv = Env.bind cenv x (Addr r) in
              preapply xs ys newenv newmem
          | [], [] -> cenv, cmem
          | _, _ -> raise (Error "InvalidArg") in
        let wenv, newmem = preapply id_list fel fenv mem' in
        let newenv = Env.bind wenv id (Proc (id_list, fexp, wenv)) in
        eval newmem newenv fexp
    | CALLR (id, iel) ->
        let id_list, fexp, fenv = lookup_env_proc env id in
        let rec preapply l ll cenv =
          match l, ll with
          | x::xs, y::ys ->
              let newenv = Env.bind cenv x (Env.lookup env y) in
              preapply xs ys newenv
          | [], [] -> cenv
          | _, _ -> raise (Error "InvalidArg") in
        let wenv = preapply id_list iel fenv in
        let newenv = Env.bind wenv id (Proc (id_list, fexp, wenv)) in
        eval mem newenv fexp
    | RECORD iel ->
        if (List.length iel) = 0 then (Unit, mem) else
        let rec construct_record rl crec cmem =
          ( match rl with
          | (id, e)::rest ->
              let (r, mem'') = Mem.alloc cmem in
              let ev, mem' = eval mem'' env e in
              let newmem = Mem.store mem' r ev in
              let nr = (fun x -> if x = id then r else crec x) in
              construct_record rest nr newmem
          | [] -> (Record crec), cmem ) in
        let res, mem' = construct_record iel (fun x -> raise (Error "Unbound")) mem in
        (res, mem')
    | FIELD (e, id) ->
        let ev, mem' = eval mem env e in
        let r = value_record ev in
        let rr = Mem.load mem' (r id) in
        (rr, mem')
    | ASSIGNF (e1, id, e2) ->
        let r, mem1 = eval mem env e1 in
        let v, mem2 = eval mem1 env e2 in
        let vr = value_record r in
        let rr = vr id in
        (v, Mem.store mem2 rr v)

  let run (mem, env, pgm) =
    let (v, _ ) = eval mem env pgm in
    v
end
