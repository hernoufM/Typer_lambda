type lambda_terme = 
    Var of string
    | Abstraction of string * lambda_terme 
    | Application of lambda_terme  * lambda_terme 

let rec string_of_lterme lt =
    match lt with
        Var(name) -> name
        | Abstraction(varname,corps) -> "λ" ^ varname ^ "." ^ string_of_lterme corps
        | Application(left, right) -> "(" ^ string_of_lterme left ^ " " ^ string_of_lterme right ^ ")";;

let pp_lterme lt = Printf.fprintf stdout "%s" (string_of_lterme lt);;

let create_var name = Var name;;

let create_abs var corps = Abstraction (var, corps);;

let create_app left right = Application (left,right);;

let fresh_var, reset_gen =
    let char_gen = ref 'a'
    and num_gen = ref 0
    in
        ((function () -> 
            let var_name = (String.make 1 !char_gen) ^
                           (if !num_gen= 0 
                           then ""
                           else (string_of_int !num_gen))
            in 
                (if !char_gen = 'z' 
                then (char_gen:='a'; num_gen:=!num_gen+1)
                else char_gen := char_of_int ((int_of_char !char_gen) + 1));
                var_name),
        (function () -> char_gen := 'a'; num_gen := 0));;     

module StringMap = Map.Make(String);;

let barendregt lt =
    let rec barendregt_rec lt rename =
        match lt with
            Var(name) -> 
                (match StringMap.find_opt name rename with
                    None -> Var name
                    | Some y -> Var y)
            | Abstraction(varname,lt) -> 
                (let new_varname = fresh_var ()
                    in
                        Abstraction (new_varname, (barendregt_rec lt (StringMap.add varname new_varname rename))))
            | Application(lt1, lt2) -> 
                Application(barendregt_rec lt1 rename, barendregt_rec lt2 rename)
    in
        barendregt_rec lt StringMap.empty;;
(* Lx.((Lx.Ly.x y) (Ly.y z)) x *)
let lambda_ex = create_abs "x" (create_app (create_app (create_abs "x" (create_abs "y" (create_app (create_var "x") (create_var "y")))) (create_abs "y" (create_app (create_var "y") (create_var "z")))) (create_var "x"));;

