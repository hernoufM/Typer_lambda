type lambda_terme = 
    Var of string
    | Abstraction of string * lambda_terme ref
    | Application of lambda_terme ref * lambda_terme ref

let rec print_lterme lt =
    match lt with
        Var(name) -> Printf.fprintf stdout "%s" name
        | Abstraction(varname,corps) -> Printf.fprintf stdout "%s" ("λ" ^ varname ^ "."); print_lterme !corps
        | Application(left, right) -> print_lterme !left; print_string " "; print_lterme !right;;

let create_var name = Var name;;

let create_abs var corps = Abstraction (var, corps);;

let create_app left right = Application (left,right);;