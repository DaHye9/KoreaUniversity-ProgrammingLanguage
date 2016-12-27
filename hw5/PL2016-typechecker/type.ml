type exp =
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

type program = exp

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty =
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns =
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ " ^ ")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x ->
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst =
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst ->
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn
 = fun tenv e ty -> 
  match e with
    | CONST (n) -> [(ty,TyInt)]
    | VAR (x) -> [(ty,tenv x)]
    | ADD (e1,e2) -> ([(ty,TyInt)]) @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
    | SUB (e1,e2) -> ([(ty,TyInt)]) @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
    | MUL (e1,e2) -> ([(ty,TyInt)]) @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
    | DIV (e1,e2) -> ([(ty,TyInt)]) @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
    | ISZERO (e1) -> ([(ty,TyBool)]) @ (gen_equations tenv e1 TyInt)
    | IF(e1,e2,e3) -> (gen_equations tenv e1 TyBool) @ (gen_equations tenv e2 ty) @ (gen_equations tenv e3 ty)
    | LET (v1,e1,e2) -> let tv1 = fresh_tyvar() in (gen_equations tenv e1 tv1) @ (gen_equations (TEnv.extend(v1,tv1) tenv) e2 ty)
    | LETREC (f,x,e1,e2) ->
      let tv1 = fresh_tyvar() in
      let tv2 = fresh_tyvar() in (gen_equations (TEnv.extend(f,TyFun(tv2,tv1)) (TEnv.extend(x,tv2) tenv)) e1 tv1) @ (gen_equations (TEnv.extend(f,TyFun(tv2,tv1)) tenv) e2 ty)
    | PROC (v1,e1) ->
      let tv1 = fresh_tyvar() in
      let tv2 = fresh_tyvar() in ([(ty,TyFun(tv1,tv2))]) @ (gen_equations (TEnv.extend(v1,tv1) tenv) e1 tv2)
    | CALL (e1,e2) -> let tv1 = fresh_tyvar() in (gen_equations tenv e1 (TyFun(tv1,ty))) @ (gen_equations tenv e2 tv1)
    | _ -> raise(Failure "TypeError")

let rec occurs : string -> typ -> bool
 = fun a t -> 
  match t with
    | TyVar b -> a = b
    | TyFun(b1,b2) -> (occurs a b1) || (occurs a b2)
    | _ -> false

let rec unify : typ -> typ -> Subst.t -> Subst.t
 = fun t1 t2 s -> 
  match (t1,t2,s) with
    | (TyInt,TyInt,s) -> s
    | (TyBool,TyBool,s) -> s
    | (TyVar a,t,s) -> 
      if occurs a t then raise(Failure "TypeError")
      else Subst.extend a t s
    | (t,TyVar a,s) -> unify (TyVar a) t s
    | (TyFun (t1,t2), TyFun (tl_,t2_),s) -> let s_ = unify t1 tl_ s in unify (Subst.apply t2 s_) (Subst.apply t2_ s_) s_
    | (_,_,_) -> raise(Failure "TypeError")

let rec unify_all : typ_eqn -> Subst.t -> Subst.t
 = fun eqn s -> 
  match eqn with
    | [] -> s
    | (t1,t2)::u -> unify_all u (unify (Subst.apply t1 s) (Subst.apply t2 s) s)

let solve : typ_eqn -> Subst.t
 = fun eqns -> unify_all eqns Subst.empty

let typeof : exp -> typ (* Do not modify this function *)
 = fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns;
          print_endline "" in
  let subst = solve eqns in
  let ty = Subst.apply new_tv subst in
   print_endline "= Substitution = ";
    Subst.print subst;
    print_endline "";
    print_endline ("Type: " ^ string_of_type ty);
    print_endline "";
    ty