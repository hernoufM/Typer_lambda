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

let pp_lterme lt = Printf.fprintf stdout "%s" (string_of_lterme lt);;

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
module StringSet = Set.Make(String);;

let barendregt lt =
    let rec barendregt_rec lt rename var_globs =
        match lt with
            Var(name) -> 
                (match StringMap.find_opt name rename with
                    None -> create_var name
                    | Some y -> create_var y)
            | Abstraction(varname,lt) -> 
                (let new_varname = ref (fresh_var ())
                in
                    while StringSet.mem !new_varname var_globs do
                        new_varname := fresh_var ()
                    done;
                    create_abs !new_varname (barendregt_rec lt (StringMap.add varname !new_varname rename) var_globs))
            | Application(lt1, lt2) -> 
                create_app (barendregt_rec lt1 rename var_globs) (barendregt_rec lt2 rename var_globs)
            | Add (a,b) -> create_add (barendregt_rec a rename var_globs) (barendregt_rec b rename var_globs)
            | Sub (a,b) -> create_sub (barendregt_rec a rename var_globs) (barendregt_rec b rename var_globs)
            | Liste lt_l -> 
                let evaluate_liste = 
                    List.map
                        (function x -> (barendregt_rec x rename var_globs))
                        lt_l
                in
                    create_liste evaluate_liste
            | Head lt_l -> create_head (barendregt_rec lt_l rename var_globs)
            | Tail lt_l -> create_tail (barendregt_rec lt_l rename var_globs)
            | Cons (elt,lt_l) -> create_cons (barendregt_rec elt rename var_globs) (barendregt_rec lt_l rename var_globs)
            | x -> x
    and variables_globals lt var_libres =
            match lt with
                Var(name) -> 
                    if StringSet.mem name var_libres
                    then StringSet.empty
                    else StringSet.singleton name
                | Abstraction(varname,corps) -> 
                    variables_globals corps (StringSet.add varname var_libres)
                | Application(lt1, lt2) -> 
                    StringSet.union (variables_globals lt1 var_libres) (variables_globals lt2 var_libres)
                | Add (a,b) ->
                    StringSet.union (variables_globals a var_libres) (variables_globals b var_libres)
                | Sub (a,b) ->
                    StringSet.union (variables_globals a var_libres) (variables_globals b var_libres)
                | Liste lt_l ->
                    List.fold_right variables_globals lt_l var_libres
                | Head lt_l -> (variables_globals lt_l var_libres)
                | Tail lt_l -> (variables_globals lt_l var_libres)
                | Cons (elt,lt_l) -> StringSet.union (variables_globals elt var_libres) (variables_globals lt_l var_libres)
                | _ -> var_libres
    in
        let var_globs = variables_globals lt StringSet.empty
        in
            barendregt_rec lt StringMap.empty var_globs;;

(* (λx.(cons (λx.x) (cons (head x) (tail x)))) [1]*)
let lambda_ex = 
    create_app
        (create_abs "x"
            (create_cons 
                (create_abs "x"
                    (create_var "x"))
                (create_cons
                    (create_head
                        (create_var "x"))
                    (create_tail
                        (create_var "x")))))
        (create_liste [create_int 1])

let rec instantie lt varname rempl =
    match lt with
        Var(name) -> 
            if name = varname 
            then rempl
            else lt
        | Abstraction(var,corps) ->
            if var = varname
            then lt
            else create_abs var (instantie corps varname rempl)
        | Application(lt1, lt2) ->
            create_app (instantie lt1 varname rempl) (instantie lt2 varname rempl)
        | Add (a,b) -> create_add (instantie a varname rempl) (instantie b varname rempl)
        | Sub (a,b) -> create_sub (instantie a varname rempl) (instantie b varname rempl)
        | Liste lt_l ->
            create_liste (List.map (function x -> instantie x varname rempl) lt_l)
        | Head lt_l -> create_head (instantie lt_l varname rempl)
        | Tail lt_l -> create_tail (instantie lt_l varname rempl)
        | Cons (elt,lt_l) -> create_cons (instantie elt varname rempl) (instantie lt_l varname rempl)
        | x -> x;;

(* ((λx.(λy.(x y))) (λy.(y z))) x *)
let lambda_ex2 = 
    create_app 
        (create_app 
            (create_abs "x" 
                (create_abs "y" 
                    (create_app 
                        (create_var "x") 
                        (create_var "y")))) 
            (create_abs "y" 
                (create_app 
                    (create_var "y") 
                    (create_var "z")))) 
        (create_var "x");;

exception Evaluation_exc of string;;

let rec isReduced lt = 
    match lt with
        Application(Abstraction(_,_), _) -> false
        | Var _ -> true
        | Abstraction _ -> true
        | Int _ -> true
        | Application(func, argument) -> (isReduced func) && (isReduced argument)
        | Liste lt_l -> List.for_all isReduced lt_l
        | _ -> false;; 

let rec ltrcbv_etape lt =
    let evaluate lt =
        let eval_lt = ref lt
        and start_time = ref (Unix.time ())
        in
            while not (isReduced !eval_lt)
                      && (Unix.time ()) -. !start_time < 0.1 do
                eval_lt := ltrcbv_etape !eval_lt;
                reset_gen ();
            done;
            if not (isReduced !eval_lt)
            then raise (Evaluation_exc ("Terme " ^ string_of_lterme lt ^ " is divergent"))
            else !eval_lt
    in
        match lt with
            Application(Abstraction(name,corps), argument) ->
                let eval_arg = ltrcbv_etape argument
                in
                    barendregt (instantie corps name eval_arg)
            | Application(func, argument) ->
                let eval_func = ltrcbv_etape func
                and eval_arg = ltrcbv_etape argument
                in
                    (match eval_func with
                        Abstraction(name, corps) -> barendregt (instantie corps name eval_arg)
                        | _ -> create_app eval_func eval_arg )
            | Add (a,b) -> 
                let eval_a = evaluate a
                and eval_b = evaluate b
                in
                    (match eval_a,eval_b with
                        Int a, Int b -> Int (a+b)
                        | _ -> raise (Evaluation_exc "Argument of '+' is not int"))
            | Sub (a,b) ->
                let eval_a = evaluate a
                and eval_b = evaluate b
                in
                    (match eval_a,eval_b with
                        Int a, Int b -> Int (a-b)
                        | _ -> raise (Evaluation_exc "Argument of '-' is not int"))
            | Liste lt_l -> create_liste (List.map evaluate lt_l)
            | Head lt_l ->
                let eval_liste = evaluate lt_l
                in
                    (match eval_liste with
                        Liste lt_l -> if lt_l = []
                                      then raise (Evaluation_exc "Argument of 'head' is empty list")
                                      else List.hd lt_l
                        | _ -> raise (Evaluation_exc "Argument of 'head' is not list"))
            | Tail lt_l ->
                let eval_liste = evaluate lt_l
                in
                    (match eval_liste with
                        Liste lt_l -> if lt_l = []
                                      then raise (Evaluation_exc "Argument of 'tail' is empty list")
                                      else create_liste (List.tl lt_l)
                        | _ -> raise (Evaluation_exc "Argument of 'tail' is not list"))
            | Cons (elt,lt_l) ->
                let eval_elt = ltrcbv_etape elt
                and eval_liste = evaluate lt_l
                in
                    (match eval_liste with
                        Liste lt_l -> create_liste (eval_elt::lt_l)
                        | _ -> raise (Evaluation_exc "Argument of 'tail' is not list"))
            | x -> x;;

(* (λx.x x x) (λx.x x x) *)
let sigma = 
    create_app 
        (create_abs "x" 
            (create_app 
                (create_app 
                    (create_var "x") 
                    (create_var "x")) 
                (create_var "x"))) 
        (create_abs "x" 
            (create_app 
                (create_app 
                    (create_var "x") 
                    (create_var "x")) 
                (create_var "x")))

let reduce_lambda lt = 
    let lambda = ref lt
    and start_time = Unix.time ()
    in
        while not (isReduced !lambda) && (Unix.time ()) -. start_time < 0.1 do
            lambda := ltrcbv_etape !lambda;
            pp_lterme !lambda;
            print_newline ();
            reset_gen ();
        done;
        print_newline();
        if not (isReduced !lambda)
        then print_endline "Time is out, lambda is divergent"
        else (print_string "Final lambda is : "; pp_lterme !lambda; print_newline ());;
