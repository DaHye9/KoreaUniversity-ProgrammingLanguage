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
  | VAR x -> (mem (env x), mem)
  | ADD(e1, e2) ->
  	begin
  		match eval e1 env mem with
  		| (Int n1, mem1) -> 
  			begin
  				match eval e2 env mem1 with
  				| (Int n2, mem2) -> (Int(n1 + n2), mem2)
  				| _ -> raise UndefSemantics
  			end
  		| _ -> raise UndefSemantics
  	end
  | SUB(e1, e2) ->
  	begin
  		match eval e1 env mem with
  		| (Int n1, mem1) -> 
  			begin
  				match eval e2 env mem1 with
  				| (Int n2, mem2) -> (Int(n1 - n2), mem2)
  				| _ -> raise UndefSemantics
  			end
  		| _ -> raise UndefSemantics
  	end
  | MUL(e1, e2) ->
  	begin
  		match eval e1 env mem with
  		| (Int n1, mem1) -> 
  			begin
  				match eval e2 env mem1 with
  				| (Int n2, mem2) -> (Int(n1 * n2), mem2)
  				| _ -> raise UndefSemantics
  			end
  		| _ -> raise UndefSemantics
  	end
  | DIV(e1, e2) ->
  	begin
  		match eval e1 env mem with
  		| (Int n1, mem1) -> 
  			begin
  				match eval e2 env mem1 with
  				| (Int n2, mem2) -> (Int(n1 / n2), mem2)
  				| _ -> raise UndefSemantics
  			end
  		| _ -> raise UndefSemantics
  	end
  | ISZERO e ->
  	begin
	  	match eval e env mem with
	  	| (Int n1, mem1) -> if n1 = 0 then (Bool true, mem1) else (Bool false, mem1)
	  	| _ -> raise UndefSemantics
	end
  | READ -> (Int(read_int()), mem)
  | IF(condition, e1, e2) -> 
  	begin
  		match eval condition env mem with
  		| (Bool b, mem1) -> if b then eval e1 env mem1 else eval e2 env mem1
  		| _ -> raise UndefSemantics
  	end
  | LET(x, e1, e2) -> 
  	begin
  		match eval e1 env mem with
  		| (v1, mem1) -> 
  			let l = new_location()
  				in eval e2 (extend_env (x,l) env) (extend_mem (l,v1) mem1)
  		| _ -> raise UndefSemantics
  	end
  | LETREC(f, x, e1, e2) -> 
  	let l = new_location()
  		in eval e2 (extend_env (f,l) env) (extend_mem (l,RecClosure(f,x,e1,env)) mem)
  | PROC(x, e) -> (Closure(x,e,env),mem)
  | CALL(e1, e2) -> 
  	begin
  		match eval e1 env mem with
	  	| (Closure(x,e,env_),mem1) -> 
	  		begin
	  			match eval e2 env mem1 with
	  			| (v, mem2) -> 
	  				let l = new_location()
	  					in eval e (extend_env (x,l) env_) (extend_mem (l,v) mem2)
	  			| _ -> raise UndefSemantics
	  		end
	  	| (RecClosure(f,x,e,env_),mem1) ->
	  		begin
	  			match eval e2 env mem1 with
	  			| (v, mem2) -> 
	  				let l1 = new_location()
	  					in let l2 = new_location()
	  						in eval e 
	  						(extend_env (f,l2) (extend_env (x,l1) env)) 
	  						(extend_mem (l2,RecClosure(f,x,e,env_)) (extend_mem (l1,v) mem))
	  			| _ -> raise UndefSemantics
	  		end
	  	| _ -> raise UndefSemantics
  	end
  | CALLREF(e1, y) ->
  	begin
  		match eval e1 env mem with
  		| (Closure(x,e,env_),mem1) -> eval e (extend_env (x,env y) env_) mem1
  		| (RecClosure(f,x,e,env_),mem1) -> 
  			let l = new_location()
  				in eval e (extend_env (f,l) (extend_env (x,env y) env_))
  				(extend_mem (l,RecClosure(f,x,e,env_)) mem1)
  		| _ -> raise UndefSemantics
  	end
  | SET(x, e) ->
  	begin
  		match eval e env mem with
  		| (v, mem1) -> (v, extend_mem (env x, v) mem1)
  		| _ -> raise UndefSemantics
  	end
  | SEQ(e1, e2) ->
  	begin
  		match eval e1 env mem with
	  	| (v1, mem1) -> eval e2 env mem1
	  	| _ -> raise UndefSemantics
  	end
  | BEGIN e -> eval e env mem
  | _ -> raise UndefSemantics

let run : program -> value
=fun pgm -> 
  let (v,m) = eval pgm empty_env empty_mem in
    v