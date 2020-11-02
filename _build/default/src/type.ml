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
            let typ = create_var_t (fresh_var_t ())
            in
                let equations = gen_equas_rec StringMap.empty lt typ
                in
                    (create_var_t "?",typ)::equations
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
        | ArrowT (typ_arg, typ_res) -> (occur_check varname typ_arg) || (occur_check varname typ_res);;

let rec substitue varname typ_rename typ =
    match typ with
        VarT name ->
            if varname = name
            then typ_rename
            else typ
        | ArrowT (typ_arg,typ_res) ->
            create_arrow_t (substitue varname typ_rename typ_arg) (substitue varname typ_rename typ_res);;

let rec substitue_partout varname typ_rename equations : equation list=
    match equations with
        [] -> []
        | (typ1,typ2)::equats -> 
            (substitue varname typ_rename typ1,substitue varname typ_rename typ2)
            ::(substitue_partout varname typ_rename equats);;

exception No_soltuions_equations;;

let i = create_abs "x" (create_var "x");;
let k = create_abs "x" (create_abs "y" (create_var "x"));;
let s = create_abs "x"
            (create_abs "y"
                (create_abs "z"
                    (create_app
                        (create_app
                            (create_var "x")
                            (create_var "z"))
                        (create_app
                            (create_var "y")
                            (create_var "z")))));;

(* λxyzt.((x (y t)) t) (z t) *)
let lambda_ex3 = 
    create_abs "x" 
        (create_abs "y" 
            (create_abs "z"
                (create_abs "t"
                    (create_app
                        (create_app
                            (create_app 
                                (create_var "x")
                                (create_app
                                    (create_var "y")
                                    (create_var "t")))
                            (create_var "t"))
                        (create_app
                            (create_var "z")
                            (create_var "t"))))));;

let unification_etape equations : equation list=
    let rec unification_etape_rec equations res =
        match equations with
            [] -> res
            | (typ1,typ2)::equats 
                when stype_egal typ1 typ2 -> unification_etape_rec equats res
            | ((VarT varname, typ) as equat)::equats -> 
                if not (occur_check varname typ)
                then if (varname = "?")
                     then unification_etape_rec equats (equat::res)
                     else unification_etape_rec 
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

let rename_grec typ =
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
    in
        rename_grec_rec typ (ref StringMap.empty);;    

let typeur lt =
    let start_time = Unix.time ()
    and equations = ref (gen_equas lt)
    in 
        let get_type_from_equations equations = 
            match equations with
                [(VarT "?",typ)] -> Some typ
                | _ -> None 
        in
            reset_gen_grec();
            while get_type_from_equations !equations = None 
                  && (Unix.time ()) -. start_time < 0.1 do
                equations := unification_etape !equations
            done;
            print_newline ();
            match get_type_from_equations !equations with
                Some typ -> (Printf.printf "Type of %s is " (string_of_lterme lt); 
                            pp_ltype (rename_grec typ); 
                            print_newline ())
                | None -> Printf.printf "Terme %s is not typable" (string_of_lterme lt);print_newline ();;
            