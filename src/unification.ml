open Types;;
open Syntax;;

let rec occur_check varname typ = 
    match typ with
        VarT name -> name = varname
        | ArrowT (typ_arg, typ_res) -> (occur_check varname typ_arg) || (occur_check varname typ_res)
        | Nat -> false
        | ListeT typ_elt -> occur_check varname typ_elt
        | Forall (vars,typ) -> 
            if not (StringSet.mem varname vars)
            then occur_check varname typ
            else false
        | UnitT -> false
        | RefT typ -> occur_check varname typ
        | WeakVarT w_info -> 
            (match !w_info with
                Not_instantied name -> name=varname
                | Instantied typ_instancied -> occur_check varname typ_instancied);;

let rec substitue varname typ_rename typ =
    match typ with
        VarT name ->
            if varname = name
            then typ_rename
            else typ
        | ArrowT (typ_arg,typ_res) ->
            create_arrow_t (substitue varname typ_rename typ_arg) (substitue varname typ_rename typ_res)
        | Nat -> create_nat
        | ListeT typ_elt -> create_liste_t (substitue varname typ_rename typ_elt)
        | Forall (vars,typ_corp) -> 
            if not (StringSet.mem varname vars)
            then create_forall vars (substitue varname typ_rename typ_corp)
            else typ
        | UnitT -> create_unit_t
        | RefT typ -> create_ref_t (substitue varname typ_rename typ)
        | WeakVarT w_info -> (* Useless? *)
            (match !w_info with
                Not_instantied name ->
                    if name=varname then w_info:=Instantied typ_rename;
                    typ
                | Instantied typ_instancied ->
                    let new_instancied = substitue varname typ_rename typ_instancied
                    in
                        w_info:=Instantied new_instancied;
                        typ)

let rec substitue_partout varname typ_rename equations : equation list=
    match equations with
        [] -> []
        | (typ1,typ2)::equats -> 
            (substitue varname typ_rename typ1,substitue varname typ_rename typ2)
            ::(substitue_partout varname typ_rename equats);;

let unification_etape equations : equation list=
    let rec unification_etape_rec equations res =
        let barendregt_forall vars typ =
            let new_typ = ref typ
            in
                StringSet.iter 
                    (function varname -> 
                        let new_var = create_var_t (new_var_t ())
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
                | (RefT t1, RefT t2)::equats ->
                    unification_etape_rec equats ((t1,t2)::res)
                | (WeakVarT weak_info, typ)::equats ->
                    (match !weak_info with
                        Not_instantied _ -> 
                            weak_info := Instantied typ;
                            unification_etape_rec equats res
                        | Instantied typ_instancied ->
                            unification_etape_rec equats ((typ_instancied,typ)::res))
                | (typ, WeakVarT weak_info)::equats ->
                    (match !weak_info with
                        Not_instantied _ -> 
                            weak_info := Instantied typ;
                            unification_etape_rec equats res
                        | Instantied typ_instancied ->
                            unification_etape_rec equats ((typ, typ_instancied)::res))
                | _ -> raise (Typage_exc "3")
    in
        unification_etape_rec equations [];;