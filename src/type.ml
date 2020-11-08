open Lambda;;

type lambda_type = 
    VarT of string
    | ArrowT of lambda_type * lambda_type
    | Nat
    | ListeT of lambda_type
    | Forall of StringSet.t * lambda_type;;

let rec string_of_ltype t =
    match t with
        VarT name -> name
        | ArrowT (ta,tr) -> "(" ^ string_of_ltype ta ^ " -> " ^ string_of_ltype tr ^")"
        | Nat -> "Nat"
        | ListeT lt -> "["^string_of_ltype lt^"]"
        | Forall (variables, lt) -> "∀" ^ (String.concat "," (StringSet.elements variables)) ^ "." ^ string_of_ltype lt;;

let pp_ltype t = Printf.fprintf stdout "%s" (string_of_ltype t);;

let create_var_t name = VarT name;;

let create_arrow_t ta tr = ArrowT (ta, tr);;

let create_liste_t lt = ListeT lt;;

let create_forall vars lt = Forall (vars,lt);;

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
        VarT name1, VarT name2 -> name1=name2
        | ArrowT (ta1,tr1), ArrowT(ta2,tr2) -> stype_egal ta1 ta2 && stype_egal tr1 tr2
        | Nat, Nat -> true
        | ListeT t1, ListeT t2 -> stype_egal t1 t2
        | _ -> false ;;

type equation = lambda_type * lambda_type;;

exception Typage_exc of string;;

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
    in
        create_forall (varaibles_glob set_type typ) typ



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
        | Nat -> false
        | ListeT typ_elt -> occur_check varname typ_elt
        | Forall (vars,typ) -> 
            if not (StringSet.mem varname vars)
            then occur_check varname typ
            else false;;

let rec substitue varname typ_rename typ =
    match typ with
        VarT name ->
            if varname = name
            then typ_rename
            else typ
        | ArrowT (typ_arg,typ_res) ->
            create_arrow_t (substitue varname typ_rename typ_arg) (substitue varname typ_rename typ_res)
        | Nat -> Nat
        | ListeT typ_elt -> create_liste_t (substitue varname typ_rename typ_elt)
        | Forall (vars,typ_corp) -> 
            if not (StringSet.mem varname vars)
            then create_forall vars (substitue varname typ_rename typ_corp)
            else typ;;

let rec substitue_partout varname typ_rename equations : equation list=
    match equations with
        [] -> []
        | (typ1,typ2)::equats -> 
            (substitue varname typ_rename typ1,substitue varname typ_rename typ2)
            ::(substitue_partout varname typ_rename equats);;

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

(* [i, i i, i i i, k i s] *)
let lambda_ex3 = 
    create_liste
        [i;
        (create_app i (create_int 5));
        (create_app (create_app i i) i);
        (create_app (create_app k i) (create_int 5))];;

let deux = 
    create_abs "f"
        (create_abs "x"
            (create_app
                (create_var "f")
                (create_app 
                    (create_var "f")
                    (create_var "x"))));;

let trois = 
    create_abs "f"
        (create_abs "x"
            (create_app
                (create_var "f")
                (create_app 
                    (create_var "f")
                    (create_app 
                        (create_var "f")
                        (create_var "x")))));;             

let puiss =
    create_abs "n"
        (create_abs "m"
            (create_abs "f"
                (create_abs "e"
                    (create_app
                        (create_app 
                            (create_app
                                (create_var "n")
                                (create_var "m"))
                            (create_var "f"))
                        (create_var "e")))));;

let puiss_ex = create_app (create_app puiss trois) deux;;

let unification_etape equations : equation list=
    let rec unification_etape_rec equations res =
        let barendregt_forall vars typ =
            let new_typ = ref typ
            in
                StringSet.iter 
                    (function varname -> 
                        let new_var = create_var_t (fresh_var_t ())
                        in new_typ := substitue varname new_var typ)
                    vars;
                !new_typ
        in 
            match equations with
                [] -> res
                | (typ1,typ2)::equats 
                    when stype_egal typ1 typ2 -> unification_etape_rec equats res
                | (Forall (vars1,typ1),Forall (vars2,typ2))::equats ->
                    unification_etape_rec equats ((barendregt_forall vars1 typ1,barendregt_forall vars2 typ2)::res)
                | (Forall (vars1,typ1),typ)::equats ->
                    unification_etape_rec equats ((barendregt_forall vars1 typ1,typ)::res)
                | (typ, Forall (vars2,typ2))::equats ->
                    unification_etape_rec equats ((typ, barendregt_forall vars2 typ2)::res)
                | ((VarT varname, typ) as equat)::equats -> 
                    if not (occur_check varname typ)
                    then if (varname = "?")
                         then unification_etape_rec equats (equat::res)
                         else unification_etape_rec 
                                (substitue_partout varname typ equats)
                                (substitue_partout varname typ res)
                    else raise (Typage_exc "1")
                | (typ, VarT varname)::equats -> 
                    if not (occur_check varname typ)
                    then unification_etape_rec 
                            (substitue_partout varname typ equats)
                            (substitue_partout varname typ res)
                    else raise (Typage_exc "2")
                | (ArrowT (typ_arg1,typ_res1),ArrowT (typ_arg2,typ_res2))::equats ->
                    unification_etape_rec  equats ((typ_arg1,typ_arg2)::(typ_res1,typ_res2)::res)
                | (ListeT elt_t1, ListeT elt_t2)::equats ->
                    unification_etape_rec equats ((elt_t1,elt_t2)::res)
                | _ -> raise (Typage_exc "3")
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
            | Nat -> Nat
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
    in
        rename_grec_rec typ (ref StringMap.empty);;    


let rec gen_equas env types_set lt : equation list =
    let rec gen_equas_rec env lt typ types_set: equation list =
        match lt with
            Var varname -> [(StringMap.find varname env, typ)]
            | Abstraction (varname, corps) -> 
                let vart_arg = create_var_t (fresh_var_t ())
                and vart_corps = create_var_t (fresh_var_t ())
                in
                    let equat = (typ, create_arrow_t vart_arg vart_corps)
                    and new_types_set = StringSet.add (string_of_ltype vart_arg) (StringSet.add (string_of_ltype vart_corps) types_set)
                    in 
                        equat::(gen_equas_rec (StringMap.add varname vart_arg env) corps vart_corps new_types_set) 
            | Application (invoc, param) -> 
                let vart_arg = create_var_t (fresh_var_t ())
                in
                    let new_types_set = StringSet.add (string_of_ltype vart_arg) types_set
                    in
                        let list_g = (gen_equas_rec env invoc (create_arrow_t vart_arg typ) new_types_set)
                        in
                            let list_d = (gen_equas_rec env param vart_arg new_types_set)
                            in 
                            list_g @ list_d
            | Int _ -> [(typ, Nat)]
            | Add (a,b) -> 
                let list_a = gen_equas_rec env a Nat types_set
                in
                    let list_b = gen_equas_rec env b Nat types_set
                    in
                        (typ,Nat)::(list_a @ list_b)
            | Sub (a,b) ->
                let list_a = gen_equas_rec env a Nat types_set
                in
                    let list_b = gen_equas_rec env b Nat types_set
                    in
                        (typ,Nat)::(list_a @ list_b)
            | Liste lt_l ->
                let vart_elt = create_var_t (fresh_var_t ())
                in
                    let new_types_set = StringSet.add (string_of_ltype vart_elt) types_set
                    in
                        (typ, create_liste_t vart_elt)::(List.concat (List.map (function elt -> gen_equas_rec env elt vart_elt new_types_set) lt_l))
            | Head lt_l ->
                let vart_elt = create_var_t (fresh_var_t ())
                in
                    let new_types_set = StringSet.add (string_of_ltype vart_elt) types_set
                    in
                        (typ,vart_elt)::(gen_equas_rec env lt_l (create_liste_t vart_elt) new_types_set)
            | Tail lt_l ->
                let vart_elt = create_var_t (fresh_var_t ())
                in
                    let new_types_set = StringSet.add (string_of_ltype vart_elt) types_set
                    in
                        (typ,create_liste_t vart_elt)::(gen_equas_rec env lt_l (create_liste_t vart_elt) new_types_set)
            | Cons (elt, lt_l) ->
                let vart_elt = create_var_t (fresh_var_t ())
                in
                    let new_types_set = StringSet.add (string_of_ltype vart_elt) types_set
                    in
                        let liste_elt = gen_equas_rec env elt vart_elt new_types_set
                        in
                                let liste_ltl = gen_equas_rec env lt_l (create_liste_t vart_elt) new_types_set
                                in
                            (typ,create_liste_t vart_elt)::(liste_elt @ liste_ltl)
            | IfZte (cond,conseq,alt) ->
                let liste_cond = gen_equas_rec env cond Nat types_set
                in
                    let liste_conseq = gen_equas_rec env conseq typ types_set
                    in
                        let liste_alt = gen_equas_rec env alt typ types_set
                        in
                            liste_cond @ (liste_conseq @ liste_alt)
            | IfEte (cond,conseq,alt) ->
                let vart_elt = create_var_t (fresh_var_t ())
                in
                    let new_types_set = StringSet.add (string_of_ltype vart_elt) types_set
                    in 
                        let liste_cond = gen_equas_rec env cond (create_forall (StringSet.singleton (string_of_ltype vart_elt)) (create_liste_t vart_elt)) new_types_set
                        in
                            let liste_conseq = gen_equas_rec env conseq typ new_types_set
                            in
                                let liste_alt = gen_equas_rec env alt typ new_types_set
                                in
                                    liste_cond @ (liste_conseq @ liste_alt) 
            | Let (varname,expr,corp) ->
                let generilised_type = generalise types_set (typage env types_set expr)
                in
                    gen_equas_rec (StringMap.add varname generilised_type env) corp typ types_set
            | Fix (Abstraction (fname, corps)) ->
                let vart_f = create_var_t (fresh_var_t ())
                in
                    let new_types_set = StringSet.add (string_of_ltype vart_f) types_set
                    in 
                        (typ,vart_f)::(gen_equas_rec (StringMap.add fname vart_f env) corps vart_f new_types_set)
            | _ -> raise (Typage_exc "4")
    in
        try 
            let typ = create_var_t (fresh_var_t ())
            in
                let equations = gen_equas_rec env lt typ (StringSet.add (string_of_ltype typ) types_set)
                in
                    (create_var_t "?",typ)::equations
        with Not_found -> raise (Typage_exc "5")
and typage env types_set lt  =
    let start_time = Unix.time ()
    and equations = ref (gen_equas env types_set lt)
    in 
        let get_type_from_equations equations = 
            match equations with
                [(VarT "?",typ)] -> Some typ
                | _ -> None 
        in
            while get_type_from_equations !equations = None 
                  && (Unix.time ()) -. start_time < 0.1 do
                equations := unification_etape !equations;
            done;
            match get_type_from_equations !equations with
                Some typ -> typ
                | None -> raise (Typage_exc "6");;

let typeur lt =
    try
        reset_gen_t ();
        reset_gen_grec ();
        let typ = typage StringMap.empty StringSet.empty lt
        in
            Printf.printf "Type of %s is : \n   %s\n" (string_of_lterme lt) (string_of_ltype (rename_grec typ))
    with Typage_exc i -> Printf.printf "Terme %s is not typable %s" (string_of_lterme lt) i;;  