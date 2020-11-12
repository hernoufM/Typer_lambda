(* Type of lambda *)
type lambda_terme = 
    Var of string
    | Abstraction of string * lambda_terme 
    | Application of lambda_terme  * lambda_terme
    | Int of int
    | Add of lambda_terme * lambda_terme
    | Sub of lambda_terme * lambda_terme
    | Liste of lambda_terme list
    | Head of lambda_terme
    | Tail of lambda_terme
    | Cons of lambda_terme * lambda_terme
    | IfZte of lambda_terme * lambda_terme * lambda_terme
    | IfEte of lambda_terme * lambda_terme * lambda_terme
    | Fix of lambda_terme
    | Let of string * lambda_terme * lambda_terme
    | Ref of lambda_terme ref 
    | Deref of lambda_terme
    | Assign of lambda_terme * lambda_terme
    | Unit;;

(* Pretty-printer *)

let rec string_of_lterme lt =
    match lt with
        Var name -> name
        | Abstraction(varname,corps) -> "(λ" ^ varname ^ "." ^ string_of_lterme corps ^ ")"
        | Application(left, right) -> "(" ^ string_of_lterme left ^ " " ^ string_of_lterme right ^ ")"
        | Int i -> string_of_int i
        | Add (a,b) -> "(" ^ string_of_lterme a ^ " + " ^ string_of_lterme b ^ ")"
        | Sub (a,b) -> "(" ^ string_of_lterme a ^ " - " ^ string_of_lterme b ^ ")"
        | Liste lt_list ->
            "[" ^ String.concat ", " (List.map string_of_lterme lt_list) ^ "]"
        | Head lt_l -> "(head " ^ string_of_lterme lt_l ^ ")"
        | Tail lt_l -> "(tail " ^ string_of_lterme lt_l ^ ")"
        | Cons (elt,lt_l) -> "(cons " ^ string_of_lterme elt ^ " " ^ string_of_lterme lt_l ^ ")"
        | IfZte (cond,conseq,alt) -> "(if_zero " ^ string_of_lterme cond ^ " then " ^ string_of_lterme conseq ^ " else " ^ string_of_lterme alt^ ")"
        | IfEte (cond,conseq,alt) -> "(if_empty " ^ string_of_lterme cond ^ " then " ^ string_of_lterme conseq ^ " else " ^ string_of_lterme alt^ ")"
        | Fix f -> "(fix " ^ string_of_lterme f ^ ")"
        | Let (var,expr,corps) -> "(let " ^ var ^ " = " ^ string_of_lterme expr ^ " in " ^ string_of_lterme corps ^ ")"
        | Ref x_ref -> "(ref " ^ string_of_lterme !x_ref ^ ")"
        | Deref x -> "!" ^ string_of_lterme x
        | Assign (x_ref,x) -> "(" ^ string_of_lterme x_ref ^ " := " ^ string_of_lterme x ^ ")"
        | Unit -> "()";;

let pp_lterme lt = Printf.fprintf stdout "%s" (string_of_lterme lt);;

(* Constructors of lambda terme *)

let create_var name = Var name;;

let create_abs var corps = Abstraction (var, corps);;

let create_app left right = Application (left,right);;

let create_int i = Int i;;

let create_add a b = Add (a, b);;

let create_sub a b = Sub (a, b);;

let create_liste lt_l = Liste lt_l;;

let create_head lt_l = Head lt_l;;

let create_tail lt_l = Tail lt_l;;

let create_cons elt lt_l = Cons (elt, lt_l);;

let create_ifZte cond conseq alt = IfZte (cond,conseq,alt);;

let create_ifEte cond conseq alt = IfEte (cond,conseq,alt);;

let create_fix f = Fix f;;

let create_let varname expr corps = Let (varname,expr,corps);;

let create_ref lt_ref = Ref (ref lt_ref);;

let create_deref lt = Deref lt;;

let create_assign lt_ref lt = Assign (lt_ref,lt);;

let create_unit = Unit;;

(* Function that says if an expression is not-expansive *)
let rec non_expansive_reduced lt =
    match lt with
        | Var _ -> true
        | Int _ -> true
        | Abstraction _ -> true
        | Liste [] -> true
        | Liste lt_l -> List.for_all non_expansive_reduced lt_l
        | Add _ -> true
        | Sub _ -> true
        | Cons (elt, lt_l) -> (non_expansive_reduced elt) && (non_expansive_reduced lt_l)
        | Head lt_l -> non_expansive_reduced lt_l
        | Tail lt_l -> non_expansive_reduced lt_l
        | Fix _ -> true
        | IfZte (_,conseq,alt) -> (non_expansive_reduced conseq) && (non_expansive_reduced alt)
        | IfEte (_,conseq,alt) -> (non_expansive_reduced conseq) && (non_expansive_reduced alt)
        | Let (_,expr,corp) -> (non_expansive_reduced expr) && (non_expansive_reduced corp)
        | Unit -> true
        | _ -> false;;

(* Evaluation exception that contains description of occured problem *)
exception Evaluation_exc of string;;

(* Map of string -> 'a module *)
module StringMap = Map.Make(String);;

(* Set of string module *)
module StringSet = Set.Make(String);;