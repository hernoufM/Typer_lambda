open Types;;
open Syntax;;
open Unification;;


let generalise set_type typ =
    let rec varaibles_glob set_type typ =
         match typ with
            VarT name -> 
                if not (StringSet.mem name set_type)
                then StringSet.singleton name
                else StringSet.empty
            | ArrowT (ta,tr) -> StringSet.union (varaibles_glob set_type ta) (varaibles_glob set_type tr)
            | Nat -> StringSet.empty
            | ListeT typ_elt -> varaibles_glob set_type typ_elt
            | Forall (vars,typ) -> varaibles_glob (StringSet.union set_type vars) typ
            | UnitT -> StringSet.empty
            | RefT typ -> varaibles_glob set_type typ
            | WeakVarT _ -> StringSet.empty (* To_check *)
    in
        create_forall (varaibles_glob set_type typ) typ

let generalise_weak set_type typ =
    let rec remplace_var_weak typ rename =
        match typ with
            VarT name ->
                if not (StringSet.mem name set_type)
                then 
                    match StringMap.find_opt name !rename with
                        None -> 
                            (let weak_var = create_weak_var_t ("_"^name)
                                in
                                rename := StringMap.add name weak_var !rename;
                                weak_var)
                        | Some var -> var
                else typ
            | ArrowT (ta,tr) -> create_arrow_t (remplace_var_weak ta rename) (remplace_var_weak tr rename)
            | Nat -> create_nat
            | ListeT typ_elt -> create_liste_t (remplace_var_weak typ_elt rename)
            | Forall _ -> raise (Typage_exc "should not occur")
            | UnitT -> create_unit_t
            | RefT typ -> create_ref_t (remplace_var_weak typ rename)
            | WeakVarT w_info -> 
                (match !w_info with
                    Not_instantied _ -> typ
                    | Instantied typ_instancied -> 
                        let new_instancied = remplace_var_weak typ_instancied rename
                        in
                            w_info := Instantied new_instancied;
                            typ)
    in
        remplace_var_weak typ (ref StringMap.empty);;






let fresh_var_grec, reset_gen_grec =
    let alphabet = ["α";"β"; "γ";"δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ"; "μ"; "ν"; "ξ"; "ο"; "π"; "ρ"; "σ"; "τ"; "υ"; "φ"; "χ"; "ψ"; "ω"]
    and ind = ref 0
    and prefix = ref ""
    in
        ((function () -> 
            if !ind = List.length alphabet then (ind:=0; prefix:= "'" ^ !prefix);
            let varname = !prefix ^ (List.nth alphabet !ind)
            in               
                ind := !ind +1;
                varname)
        , function () -> ind := 0; prefix := "");;

let rec gen_equas env lt : equation list =
    let rec gen_equas_rec env lt typ: equation list =
            match lt with
                Var varname -> [(StringMap.find varname env, typ)]
                | Abstraction (varname, corps) -> 
                    let vart_arg = create_var_t (new_var_t ())
                    and vart_corps = create_var_t (new_var_t ())
                    in
                        let equat = (typ, create_arrow_t vart_arg vart_corps)
                        in 
                            equat::(gen_equas_rec (StringMap.add varname vart_arg env) corps vart_corps) 
                | Application (invoc, param) -> 
                    let vart_arg = create_var_t (new_var_t ())
                    in
                        let list_g = (gen_equas_rec env invoc (create_arrow_t vart_arg typ))
                        in
                            let list_d = (gen_equas_rec env param vart_arg)
                            in 
                                list_g @ list_d
                | Int _ -> [(typ, create_nat)]
                | Add (a,b) -> 
                    let list_a = gen_equas_rec env a create_nat
                    in
                        let list_b = gen_equas_rec env b create_nat 
                        in
                            (typ,create_nat )::(list_a @ list_b)
                | Sub (a,b) ->
                    let list_a = gen_equas_rec env a create_nat 
                    in
                        let list_b = gen_equas_rec env b create_nat 
                        in
                            (typ,create_nat )::(list_a @ list_b)
                | Liste lt_l ->
                    let vart_elt = create_var_t (new_var_t ())
                    in
                        (typ, create_liste_t vart_elt)::(List.concat (List.map (function elt -> gen_equas_rec env elt vart_elt) lt_l))
                | Head lt_l ->
                    let vart_elt = create_var_t (new_var_t ())
                    in
                        (typ,vart_elt)::(gen_equas_rec env lt_l (create_liste_t vart_elt))
                | Tail lt_l ->
                    let vart_elt = create_var_t (new_var_t ())
                    in
                        (typ,create_liste_t vart_elt)::(gen_equas_rec env lt_l (create_liste_t vart_elt))
                | Cons (elt, lt_l) ->
                    let vart_elt = create_var_t (new_var_t ())
                    in
                        let liste_elt = gen_equas_rec env elt vart_elt 
                        in
                            let liste_ltl = gen_equas_rec env lt_l (create_liste_t vart_elt)
                            in
                                (typ,create_liste_t vart_elt)::(liste_elt @ liste_ltl)
                | IfZte (cond,conseq,alt) ->
                    let liste_cond = gen_equas_rec env cond create_nat
                    in
                        let liste_conseq = gen_equas_rec env conseq typ 
                        in
                            let liste_alt = gen_equas_rec env alt typ 
                            in
                                liste_cond @ (liste_conseq @ liste_alt)
                | IfEte (cond,conseq,alt) ->
                    let vart_elt = create_var_t (new_var_t ())
                    in
                        let liste_cond = gen_equas_rec env cond (create_forall (StringSet.singleton (string_of_ltype vart_elt)) (create_liste_t vart_elt))
                        in
                            let liste_conseq = gen_equas_rec env conseq typ 
                            in
                                let liste_alt = gen_equas_rec env alt typ 
                                in
                                    liste_cond @ (liste_conseq @ liste_alt) 
                | Fix (Abstraction (fname, corps)) ->
                    let vart_f = create_var_t (new_var_t ())
                    in
                        (typ,vart_f)::(gen_equas_rec (StringMap.add fname vart_f env) corps vart_f)
                | Let (varname,expr,corp) ->
                    if non_expansive_reduced expr
                    then
                        let old_types_set = !types_set
                        in 
                            let generilised_type = generalise old_types_set (typage env expr)
                            in
                                gen_equas_rec (StringMap.add varname generilised_type env) corp typ
                    else
                        let old_types_set = !types_set
                        in 
                            let weak_type = generalise_weak old_types_set (typage env expr)
                            in
                                gen_equas_rec (StringMap.add varname weak_type env) corp typ
                | Ref lt_ref -> 
                    let var_t = create_var_t (new_var_t ())
                    in
                        (typ, create_ref_t var_t)::(gen_equas_rec env !lt_ref var_t)
                | Deref lt ->
                    let var_t = create_var_t (new_var_t ())
                    in
                        (typ, var_t)::(gen_equas_rec env lt (create_ref_t var_t))
                | Assign (lt_ref,lt) ->
                    let var_t = create_var_t (new_var_t ())
                    in
                        let liste_lt_ref = gen_equas_rec env lt_ref (create_ref_t var_t)
                        in
                            let liste_lt = gen_equas_rec env lt var_t
                            in
                                (typ, create_unit_t)::(liste_lt_ref @ liste_lt)
                | _ -> raise (Typage_exc "4")
        in
            try 
                let typ = create_var_t (new_var_t ())
                in
                    let equations = gen_equas_rec env lt typ 
                    in
                        (create_var_t "?",typ)::equations
            with Not_found -> raise (Typage_exc "5")
    and typage env lt =
        let start_time = Unix.time ()
        and equations = ref (gen_equas env lt)
        and i = ref 0
        in 
            let get_type_from_equations equations = 
                match equations with
                    [(VarT "?",typ)] -> Some typ
                    | _ -> None 
            in
                Printf.printf "Typage of %s:\n\n" (string_of_lterme lt);
                Printf.printf "Equations:\n";
                pp_equation_list !equations;
                Printf.printf "\n";
                while get_type_from_equations !equations = None 
                    && (Unix.time ()) -. start_time < 0.1 do
                    equations := unification_etape !equations;
                    Printf.printf "Tours %d\n" !i;
                    pp_equation_list !equations;
                    i:=!i+1;
                    Printf.printf "\n"
                done;
                Printf.printf "\n\n";
                match get_type_from_equations !equations with
                    Some typ -> typ
                    | None -> raise (Typage_exc "6");;

let rename_grec typ =
    let renamed_weak = ref []
    in  
        let rec rename_grec_rec typ rename =
            match typ with
                VarT varname -> 
                    (match StringMap.find_opt varname !rename with
                        Some var -> var
                        | None -> 
                            let new_var = create_var_t (fresh_var_grec ())
                            in
                                rename:=StringMap.add varname new_var !rename;
                                new_var)
                | ArrowT (typ1,typ2) -> create_arrow_t (rename_grec_rec typ1 rename) (rename_grec_rec typ2 rename)
                | Nat -> create_nat
                | ListeT typ_elt -> create_liste_t (rename_grec_rec typ_elt rename)
                | Forall (vars,typ) ->
                    let new_vars = ref StringSet.empty
                    and new_rename = ref !rename
                    in 
                        StringSet.iter 
                            (function varname -> 
                                let new_var = create_var_t (fresh_var_grec ())
                                in
                                    new_vars := StringSet.add (string_of_ltype new_var) !new_vars;
                                    new_rename := StringMap.add varname new_var !rename) 
                            vars;
                        create_forall !new_vars (rename_grec_rec typ new_rename)
                | UnitT -> create_unit_t
                | RefT typ -> create_ref_t (rename_grec_rec typ rename) 
                | WeakVarT weak_info ->
                    if List.mem typ !renamed_weak
                    then typ
                    else
                        (renamed_weak := typ::!renamed_weak; 
                        (match !weak_info with
                            Not_instantied _ -> 
                            let new_var_name = "_" ^ fresh_var_grec ()
                            in 
                                weak_info := Not_instantied new_var_name;
                                typ
                            | Instantied typ_instancied ->
                                weak_info := Instantied (rename_grec_rec typ_instancied rename);
                                typ));          
        in
            rename_grec_rec typ (ref StringMap.empty);;    

let typeur (lt:lambda_terme) =
    try
        reset_gen_t ();
        reset_gen_grec ();
        let typ = typage StringMap.empty lt
        in
            Printf.printf "Type of %s is : \n   %s\n" (string_of_lterme lt) (string_of_ltype (rename_grec typ))
    with 
        Typage_exc i -> Printf.printf "Terme %s is not typable %s" (string_of_lterme lt) i;;  