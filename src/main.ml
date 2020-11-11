open Evaluateur;;
open Syntax;;
open Typeur;;

let i = create_abs "x" (create_var "x")

let k = create_abs "x" (create_abs "y" (create_var "x"))

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
let () = ();; 
