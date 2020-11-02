open Lambda;;

type lambda_type = 
    VarT of string
    | ArrowT of lambda_type * lambda_type;;

let rec pp_ltype t =
    match t with
        VarT name -> Printf.printf "%s" name
        | ArrowT (ta,tr) -> Printf.printf "("; pp_ltype ta; Printf.printf " -> "; pp_ltype tr; Printf.printf ")";; 

let create_var_t name = VarT name;;

let create_arrow_t ta tr = ArrowT (ta, tr);;

let fresh_var_t, reset_gen_t =
    let num_gen = ref 0
    in
        ((function () -> 
            let varname = "T"^(string_of_int !num_gen)
            in
                num_gen:=!num_gen+1;
                varname),
        (function () -> num_gen := 0));;     

let rec stype_egal t1 t2 =
    match t1,t2 with
        (VarT name1, VarT name2) -> name1=name2
        | (ArrowT (ta1,tr1), ArrowT(ta2,tr2)) -> stype_egal ta1 ta2 && stype_egal tr1 tr2
        | _ -> false;;

type equation = lambda_type * lambda_type;;

exception Variable_global_exc;;

let gen_equas lt : equation list =
    let rec gen_equas_rec env lt typ =
        match lt with
            Var varname -> [(StringMap.find varname env, typ)]
            | Abstraction (varname, corps) -> 
                let vart_arg = create_var_t (fresh_var_t ())
                and vart_corps = create_var_t (fresh_var_t ())
                in
                    let equat = (typ, create_arrow_t vart_arg vart_corps)
                    in 
                        equat::(gen_equas_rec (StringMap.add varname vart_arg env) corps vart_corps) 
            | Application (invoc, param) -> 
                let vart_arg = create_var_t (fresh_var_t ())
                in
                    let list_g = (gen_equas_rec env invoc (create_arrow_t vart_arg typ))
                    in
                        let list_d = (gen_equas_rec env param vart_arg)
                        in 
                            list_g @ list_d
    in
        reset_gen_t ();
        try 
            gen_equas_rec StringMap.empty lt (create_var_t (fresh_var_t ())) 
        with Not_found -> raise Variable_global_exc;;

let rec pp_equation_list equat_list =
    match equat_list with
        [] -> ()
        | (typ1,typ2)::equats -> 
            pp_ltype typ1;
            Printf.printf " = ";
            pp_ltype typ2;
            print_newline ();
            pp_equation_list equats;;

let rec occur_check varname typ = 
    match typ with
        VarT name -> name = varname
        | ArrowT (typ_arg, typ_res) -> (occur_check varname typ_arg) || (occur_check varname typ_res)

let rec substitue varname typ_rename typ =
    match typ with
        VarT name ->
            if varname = name
            then typ_rename
            else typ
        | ArrowT (typ_arg,typ_res) ->
            create_arrow_t (substitue varname typ_rename typ_arg) (substitue varname typ_rename typ_res)

let rec substitue_partout varname typ_rename equations : equation list=
    match equations with
        [] -> []
        | (typ1,typ2)::equats -> 
            (substitue varname typ_rename typ1,substitue varname typ_rename typ2)
            ::(substitue_partout varname typ_rename equats)

exception No_soltuions_equations;;

let unification_etape equations : equation list=
    let rec unification_etape_rec equations res =
        match equations with
            [] -> []
            | (typ1,typ2)::equats 
                when stype_egal typ1 typ2 -> unification_etape_rec equats res
            | (VarT varname, typ)::equats -> 
                if not (occur_check varname typ)
                then unification_etape_rec 
                        (substitue_partout varname typ equats)
                        (substitue_partout varname typ res)
                else raise No_soltuions_equations
            | (typ, VarT varname)::equats -> 
                if not (occur_check varname typ)
                then unification_etape_rec 
                        (substitue_partout varname typ equats)
                        (substitue_partout varname typ res)
                else raise No_soltuions_equations
            | (ArrowT (typ_arg1,typ_res1),ArrowT (typ_arg2,typ_res2))::equats ->
                unification_etape_rec  equats ((typ_arg1,typ_arg2)::(typ_res1,typ_res2)::res)
    in
        unification_etape_rec equations [];;