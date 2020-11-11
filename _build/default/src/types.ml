open Syntax;;

type lambda_type = 
    VarT of string
    | ArrowT of lambda_type * lambda_type
    | Nat
    | ListeT of lambda_type
    | Forall of StringSet.t * lambda_type
    | UnitT
    | RefT of lambda_type
    | WeakVarT of weak_var_info ref
and weak_var_info =
    Not_instantied of string
    | Instantied of lambda_type;;

let rec string_of_ltype t =
    match t with
        VarT name -> name
        | ArrowT (ta,tr) -> "(" ^ string_of_ltype ta ^ " -> " ^ string_of_ltype tr ^")"
        | Nat -> "Nat"
        | ListeT lt -> "["^string_of_ltype lt^"]"
        | Forall (variables, lt) -> "∀" ^ (String.concat "," (StringSet.elements variables)) ^ "." ^ string_of_ltype lt
        | UnitT -> "unit"
        | RefT lt -> string_of_ltype lt ^ " ref"
        | WeakVarT wi_ref -> (match !wi_ref with
                                Not_instantied varname -> "weak"^varname
                                | Instantied lt -> string_of_ltype lt);;

let pp_ltype t = Printf.fprintf stdout "%s" (string_of_ltype t);;

let create_var_t name = VarT name;;

let create_arrow_t ta tr = ArrowT (ta, tr);;

let create_nat = Nat

let create_liste_t lt = ListeT lt;;

let create_forall vars lt = Forall (vars,lt);;

let create_unit_t = UnitT;;

let create_ref_t lt = RefT lt;;

let create_weak_var_t name = WeakVarT (ref (Not_instantied name));;

let rec stype_egal t1 t2 =
    match t1,t2 with
        VarT name1, VarT name2 -> name1=name2
        | ArrowT (ta1,tr1), ArrowT(ta2,tr2) -> stype_egal ta1 ta2 && stype_egal tr1 tr2
        | Nat, Nat -> true
        | ListeT t1, ListeT t2 -> stype_egal t1 t2
        | UnitT,UnitT -> true
        | RefT t1, RefT t2 -> stype_egal t1 t2
        | WeakVarT w_info1, WeakVarT w_info2 -> w_info1=w_info2
        | _ -> false ;;

exception Typage_exc of string;;

type equation = lambda_type * lambda_type;;

let rec pp_equation_list equat_list =
    match equat_list with
        [] -> ()
        | (typ1,typ2)::equats -> 
            pp_ltype typ1;
            Printf.printf " = ";
            pp_ltype typ2;
            print_newline ();
            pp_equation_list equats;;


let types_set = ref StringSet.empty

let fresh_var_t, reset_gen_t =
    let num_gen = ref 0
    in
        ((function () -> 
            let varname = "T"^(string_of_int !num_gen)
            in
                num_gen:=!num_gen+1;
                varname),
        (function () -> num_gen := 0));;  

let new_var_t () = 
    let varname = fresh_var_t () 
    in 
        types_set := StringSet.add varname !types_set; 
        varname

   