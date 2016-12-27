exception UndefSemantics

type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
  | CALLREF of exp * var
  | SET of var * exp
  | SEQ of exp * exp
  | BEGIN of exp
and var = string

type value = 
    Int of int 
  | Bool of bool 
  | Closure of var * exp * env 
  | RecClosure of var * var * exp * env
and env = var -> loc
and loc = int
and mem = loc -> value

(*********************************)
(* implementation of environment *)
(*********************************)
(* empty env *)
let empty_env = fun x -> raise (Failure "Environment is empty")
(* extend the environment e with the binding (x,v), where x is a varaible and v is a value *)
let extend_env (x,v) e = fun y -> if x = y then v else (e y)
(* look up the environment e for the variable x *)
let apply_env e x = e x

(*********************************)
(* implementation of memory      *)
(*********************************)
let empty_mem = fun _ -> raise (Failure "Memory is empty")
let extend_mem (l,v) m = fun y -> if l = y then v else (m y)
let apply_mem m l = m l

(* NOTE: you don't need to understand how env and mem work *)

let counter = ref 0

(* calling 'new_location' produces a fresh memory location *)
let new_location () = counter:=!counter+1;!counter

let value2str v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Closure (x,e,env) -> "Closure "
  | RecClosure (f,x,e,env) -> "RecClosure "^f


(* TODO: Implement this function *)
let rec eval : exp -> env -> mem -> value * mem
=fun exp env mem -> 
  match exp with
  | CONST n -> (Int n, mem)
  | _ -> raise (Failure "Unimplemented")

let run : program -> value
=fun pgm -> 
  let (v,m) = eval pgm empty_env empty_mem in
    v
