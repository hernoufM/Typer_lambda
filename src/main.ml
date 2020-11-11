open Syntax;;
open Evaluateur;;
open Typeur;;

(* i = λx.x *)
let i = create_abs "x" (create_var "x");;

(* app = λx.λy.(x y) *)
let app = 
    create_abs "x" 
        (create_abs "y" 
            (create_app 
                (create_var "x") 
                (create_var "y")));;

(* k = λx.λy.x *)
let k = create_abs "x" (create_abs "y" (create_var "x"));;

(* s = λx.λy.λz.((x z) (y z))  *)
let s =
    create_abs "x"
        (create_abs "y"
            (create_abs "z"
                (create_app
                    (create_app
                        (create_var "x")
                        (create_var "z"))
                    (create_app
                        (create_var "y")
                        (create_var "z")))));;

(* s k k *)
let s_k_k_ex = create_app (create_app s k) k;;

(* delta = λx.(x x) *)
let delta = create_abs "x" (create_app (create_var "x") (create_var "x"));;

(* omega = delta delta *)
let omega = create_app delta delta;;

(* k i omega *)
let k_i_om_ex = create_app (create_app k i) omega;;

(* λx.x x x *)
let triplet_ex =
    create_abs "x"
        (create_app
            (create_app 
                (create_var "x")
                (create_var "x"))
            (create_var "x"));;

(* s i i i *)
let s_i_i_i_ex = create_app (create_app (create_app s i) i) i;;

(* puisse trois deux *)
let puiss_lambda_ex = 
    (* λf.λx.f (f x) *)
    let deux = 
        create_abs "f"
            (create_abs "x"
                (create_app
                    (create_var "f")
                    (create_app 
                        (create_var "f")
                        (create_var "x"))))
    (* λf.λx.f (f (f x)) *)
    and trois = 
        create_abs "f"
            (create_abs "x"
                (create_app
                    (create_var "f")
                    (create_app 
                        (create_var "f")
                        (create_app 
                            (create_var "f")
                            (create_var "x")))))
    (* λn.λm.λf.λe.(n m) f e *)
    and puiss =
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
                            (create_var "e")))))
    in
        create_app (create_app puiss trois) deux;;

(* (λx.λy.(((λx.λy.x) x y) + ((λx.λy.y) x y))) 7 5 *)
let add_ex = 
    create_app
        (create_app
            (create_abs "x"
                (create_abs "y"
                    (create_sub
                        (create_app
                            (create_app
                                (create_abs "x"
                                    (create_abs "y"
                                        (create_var "x")))
                                (create_var "x"))
                            (create_var "y"))
                        (create_app
                            (create_app
                                (create_abs "x"
                                    (create_abs "y"
                                        (create_var "y")))
                                (create_var "x"))
                            (create_var "y")))))
            (create_int 7))
        (create_int 5);;

(* [i, i i, i i i, k i s] *)
let liste_ex = 
    create_liste
        [i;
        (create_app i i);
        (create_app (create_app i i) i);
        (create_app (create_app k i) (create_int 5))];;

(* (λx.[(0+x),(0-x),(λx.x) x]) 3*)
let liste2_ex = 
    create_app
        (create_abs "x"
            (create_liste
                [create_add
                    (create_int 0)
                    (create_var "x");
                create_sub
                    (create_int 0)
                    (create_var "x");
                create_app
                    (create_abs "x"
                        (create_var "x"))
                    (create_var "x")]))
        (create_int 3);;

(* fix (λmap.λf.λl.if_empty l then [] else (cons (f (head l)) (map (tail l))) ) *)
let map =
    create_fix
        (create_abs "map"
            (create_abs "f"
                (create_abs "l"
                    (create_ifEte
                        (create_var "l")
                        (create_liste [])
                        (create_cons
                            (create_app
                                (create_var "f")
                                (create_head
                                    (create_var "l")))
                            (create_app
                                (create_app 
                                    (create_var "map")
                                    (create_var "f"))
                                (create_tail
                                    (create_var "l"))))))));;
(* map (λx.x+1) [1,2,3]*)
let map_ex = 
    create_app 
        (create_app    
            map 
            (create_abs "x" 
                (create_add 
                    (create_var "x")
                    (create_int 1))))
        (create_liste [create_int 1; create_int 2; create_int 3]);;

(*  (λx.cons ((λx.x) 3) (cons (head x) (tail x))) [1]*)
let list_op_ex = 
    create_app
        (create_abs "x"
            (create_cons 
                (create_app
                    (create_abs "x"
                        (create_var "x"))
                    (create_int 3))
                (create_cons
                    (create_head
                        (create_var "x"))
                    (create_tail
                        (create_var "x")))))
        (create_liste [create_int 1]);;

(*  if_zero ((λx.x 1) - 1) then 5 else (head []) *)
let if_zero_ex = 
    create_ifZte
        (create_sub
            (create_app
                (create_abs "x"
                    (create_var "x"))
                (create_int 1))
            (create_int 1))
        (create_int 5)
        (create_head
            (create_liste []));;

(*  Evaluation : KO
    if_zero ((λx.x 1) + 1) then 5 else (head [])) *)
let if_zero_ko_ex = 
    create_ifZte
        (create_add
            (create_app
                (create_abs "x"
                    (create_var "x"))
                (create_int 1))
            (create_int 1))
        (create_int 5)
        (create_head
            (create_liste [create_abs "x" (create_var "x")]));;

(*  if_empty (tail [1]) then 5 else (head []) *)
let if_empty_ex = 
    create_ifEte
        (create_tail
            (create_liste [create_int 1]))
        (create_int 5)
        (create_head
            (create_liste []));;

(*  (fix (λsum.λx.if_zero x then 0 else ((sum (x-1))+ x))) 100 *)
let sum_100_ex = 
    create_app
        (create_fix
            (create_abs "sum"
                (create_abs "x"
                    (create_ifZte
                        (create_var "x")
                        (create_int 0)
                        (create_add
                            (create_app
                                (create_var "sum")
                                (create_sub
                                    (create_var "x")
                                    (create_int 1)))
                            (create_var "x"))))))
        (create_int 100);;

(*  let x = (head [4]) in (λx.(x+x)) x *)
let let1_ex = 
    create_let "x"
        (create_head
            (create_liste
                [create_int 4]))
        (create_app
            (create_abs "x"
                (create_add
                    (create_var "x")
                    (create_var "x")))
            (create_var "x"));;

(*  let f = (λx.x) in (f f) 3 *)
let let2_ex = 
    create_let "f"
        (create_abs "x"
            (create_var "x"))
        (create_app
            (create_app 
                (create_var "f")
                (create_var "f"))
            (create_int 3));;

(*  let add = (λx.λy.x+y) in let add_3 = add 3 in add_3 5 *)
let let3_ex = 
    create_let "add"
        (create_abs "x"
            (create_abs "y"
                (create_add
                    (create_var "x")
                    (create_var "y"))))
        (create_let "add_3"
            (create_app
                (create_var "add")
                (create_int 3))
            (create_app
                (create_var "add_3")
                (create_int 5)));;

(*  let add = (λx.λy.x+y) in let add_3 = add 3 in add_3 *)
let let4_ex = 
    create_let "add"
        (create_abs "x"
            (create_abs "y"
                (create_add
                    (create_var "x")
                    (create_var "y"))))
        (create_let "add_3"
            (create_app
                (create_var "add")
                (create_int 3))
            (create_var "add_3"));;

(* let l = [] in let l1 = (cons (λx.x) l) in  let l2 = (cons 5 l) in ((head l1) (head l2)) *)
let let5_ex =
    create_let "l"
        (create_liste [])
        (create_let "l1"
            (create_cons
                (create_abs "x"
                    (create_var "x"))
                (create_var "l"))
            (create_let "l2"
                (create_cons 
                    (create_int 5)
                    (create_var "l"))
                (create_app 
                    (create_head
                        (create_var "l1"))
                    (create_head
                        (create_var "l2")))));;

(* let x = ref 2 in let y = ref 5 in let _ = x:=!x+8 in let _ = y=!y+2 in !x-!y *)
let ref_deref_assign_ex =
    create_let "x"
        (create_ref
            (create_int 2))
        (create_let "y"
            (create_ref
                (create_int 5))
            (create_let "_"
                (create_assign
                    (create_var "x")
                    (create_add
                        (create_deref
                            (create_var "x"))
                        (create_int 8)))
                (create_let "_"
                    (create_assign
                        (create_var "y")
                        (create_add
                            (create_deref
                                (create_var "y"))
                            (create_int 5)))
                    (create_sub
                        (create_deref
                            (create_var "x"))
                        (create_deref
                            (create_var "y"))))));;

(* Polymorphisme faible (4.6)   
   Typage : ECHEC
   let l = ref [] in let _ = l:=[(λx.x)] in (head !l) + 2 *)
let poly_faible1_ex =
    create_let "l"
        (create_ref
            (create_liste []))
        (create_let "_"
            (create_assign
                (create_var "l")
                (create_liste
                    [create_abs "x"
                        (create_var "x")]))
            (create_add
                (create_head
                    (create_deref
                        (create_var "l")))
                (create_int 2)));;

(* Polymorphisme faible (example de cours)   
   Typage : ECHEC
   let x = ref (λx.x) in let _ = x:=λx.(x+1) in (!x 5) *)
let poly_faible2_ex =
    create_let "x"
        (create_ref 
            (create_abs "x"
                (create_var "x")))
        (create_let "_"
            (create_assign
                (create_var "x")
                (create_abs "x"
                    (create_add
                        (create_var "x")
                        (create_int 1))))
            (create_app
                (create_deref
                    (create_var "x"))
                (create_liste [])));;

(* Polymorphisme faible (exemple de cours)
   let a = λx.λy.(x y) in let g = a (λx.x) in g *)
let poly_faible3_ex =
    create_let "a"
        (create_abs "x"
            (create_abs "y"
                (create_app
                    (create_var "x")
                    (create_var "y"))))
        (create_let "g"
            (create_app 
                (create_var "a")
                (create_abs "x"
                    (create_var "x")))
            (create_var "g"));;

(* Polymorphisme faible (exemple de cours) suite
   let a = λx.λy.(x y) in let g = a (λx.x) in let _ = g 5 in g
   *)
let poly_faible3_2_ex =
    create_let "a"
        (create_abs "x"
            (create_abs "y"
                (create_app
                    (create_var "x")
                    (create_var "y"))))
        (create_let "g"
            (create_app 
                (create_var "a")
                (create_abs "x"
                    (create_var "x")))
            (create_let "_"
                (create_app
                    (create_var "g")
                    (create_int 5))
                (create_var "g")));;


let lambda_termes = [
        ("i",i);
        ("app",app);
        ("k",k);
        ("s",s);
        ("s_k_k_ex",s_k_k_ex);
        ("delta",delta);
        ("omega",omega);
        ("k_i_om_ex",k_i_om_ex);
        ("triplet_ex",triplet_ex);
        ("s_i_i_i_ex",s_i_i_i_ex);
        ("puiss_lambda_ex",puiss_lambda_ex);
        ("add_ex",add_ex);
        ("liste_ex",liste_ex);
        ("liste2_ex",liste2_ex);
        ("map",map);
        ("map_ex",map_ex);
        ("list_op_ex",list_op_ex);
        ("if_zero_ex",if_zero_ex);
        ("if_zero_ko_ex",if_zero_ko_ex);
        ("if_empty_ex",if_empty_ex);
        ("sum_100_ex",sum_100_ex);
        ("let1_ex",let1_ex);
        ("let2_ex",let2_ex);
        ("let3_ex",let3_ex);
        ("let4_ex",let4_ex);
        ("let5_ex",let5_ex);
        ("ref_deref_assign_ex",ref_deref_assign_ex);
        ("poly_faible1_ex",poly_faible1_ex);
        ("poly_faible2_ex",poly_faible2_ex);
        ("poly_faible3_ex",poly_faible3_ex);
        ("poly_faible3_2_ex",poly_faible3_2_ex)
    ];;

let clear_screen () =
    for _ = 0 to 100 do
        Printf.printf "\n"
    done;;

let choix_0_n n =
   let choix = ref (-1)
   in
      while !choix < 0 || !choix > n do
        try
            Printf.printf ":> ";
            choix := read_int ();
        with Failure _ -> ()
      done;
      !choix;;

let choix_lambda_menu () =
    let choix_lambda = ref (-1)
    and exit = ref false
    and nombre_choix = List.length lambda_termes
    in  
        while not !exit do
            clear_screen ();
            Printf.printf "\n\n";
            Printf.printf "Choose your lambda term:\n";
            List.iteri 
                (fun i (_,lt) -> Printf.printf " (%d) %s\n" i (string_of_lterme lt)) 
                lambda_termes; 
            Printf.printf " (%d) Exit to main menu\n" nombre_choix;
            choix_lambda := choix_0_n nombre_choix;
            if !choix_lambda = nombre_choix
            then exit:=true
            else
               (let (_, lt) = List.nth lambda_termes !choix_lambda
                and type_correct = ref true 
                in
                    clear_screen ();
                    Printf.printf "========================== Typer ==========================\n\n";
                    type_correct := typeur lt;
                    if !type_correct 
                    then 
                         (Printf.printf "\n\n========================== Evaluateur ==========================\n\n";
                          evaluateur lt;
                          Printf.printf "\n\n============================== END ==============================n\n")
                    else
                        Printf.printf "\n\n============================== END ==============================n\n";
                    Printf.printf " (0) To lambdas\n";
                    let _ = choix_0_n 0 in ())
        done;;

let () =
    let choix_op = ref (-1)
    in    
        while true do 
            clear_screen ();
            Printf.printf "Choose your operation:\n";
            Printf.printf " (0) To type and evaluate lambda term\n";
            Printf.printf " (1) Exit\n";
            choix_op := choix_0_n 1;
            match !choix_op with
                0 -> choix_lambda_menu ();
                | _ -> exit(0);
        done;;

    
