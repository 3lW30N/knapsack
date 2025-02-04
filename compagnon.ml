(* ALGORITHME DE BRANCH-AND-BOUND POUR KNAPSACK *)

(* 5. Interlude : implémentation d’un module pour les rationnels *)

module Q = struct
  type t = int * int
  (* (a, b) encode a/b*)
  (* invariant : a ∧ b = 1 et b > 0 et si a = 0 alors b = 1 *)
  (* NB: vu l'invariant, l'égalité syntaxique de OCaml (a, b)=(c, d)*)
  (*     encode en fait l'égalité sémantique de Q : a/b = c/d *)
  let print ((a, b): t) = Printf.printf "%d/%d" a b
  let dirty_print ((a, b): t) = Printf.printf "%.2f" ((float_of_int a) /. (float_of_int b))
  let opp (p: t) : t =
    let (a, b) = p in (-a, b)
    
  let (+) (p: t) (q: t) : t =
  let (a, b) = p in
  let (c, d) = q in
  if (a, b) = (0, 0) then (c,d)
  else if (c, d) = (0, 0) then (a,b)
  else
    ( a * d + b * c, b * d)
      
  let (-) (p: t) (q: t) : t =
    p + (opp q)

  let (//) (p: t) (q: t) : t =
    let (a, b) = p in
    let (c, d) = q in
    ( a * d , b * c)
  
  let ( ** ) (p: t) (q: t) : t =
    let (a, b) = p in
    let (c, d) = q in
    ( a*c , b*d)

  
  let rat (x: int) : t = (x, 1)

  let signe (p: t) : int =
    let (a, b) = p in
    if a > 0 then 1
    else if a = 0 then 0
    else -1

  let (<) (p: t) (q: t) : bool = (signe (q - p)) = 1
  let (<=) (p: t) (q: t) : bool = (signe (q - p)) = 1 || (signe(q - p)) = 0

  let entier (p: t) : bool =
    let (a, b) = p in b = 1 || a = b || a mod b = 0

end

type sad =
  {
    n  : int;                (* le nombre d’objets                  *)
    wi : int array;          (* le tableau des poids, de taille n   *)
    vi : int array;          (* le tableau des valeurs, de taille n *)
    p  : int                 (* le poids maximal du sac à dos, >=0  *)
}

let ex =
  {
    n  = 6;
    wi = [|6  ; 8 ; 10; 14; 2; 5|] ;
    vi = [|13 ; 16; 19; 24; 3; 5|] ;
    p  = 20;
  }


type masque = bool option array

type solution = bool array

type qsolution = Q.t array

(* Fonction d'affichage d'un tableau *)
let affiche_array_param (pp: 'a -> unit) (m: 'a array) =
  let n = Array.length m in
  Printf.printf "[|";
  for i = 0 to n-2 do
    pp m.(i) ; Printf.printf "; "
  done;
  if n > 0 then pp m.(n-1);
  Printf.printf "|]"

(* Affiche un masque *)
let affiche_masque (m: masque) =
  let print_masque_atom (bo: bool option) =
    match bo with
    | None        -> Printf.printf " "
    | Some(true)  -> Printf.printf "Y"
    | Some(false) -> Printf.printf "N"
  in
  affiche_array_param print_masque_atom m

(* Affichage d'une solution entière *)
let affiche_solution (m: solution) =
  let print_solution_atom (bo: bool) =
    match bo with
    | true  -> Printf.printf "1"
    | false -> Printf.printf "0"
  in
  affiche_array_param print_solution_atom m

(* Affichage d'une solution fractionnaire *)
let affiche_qsolution (m: qsolution) =
  affiche_array_param Q.print m


(* 1. Prise en main *)

(* Test de validité d'une instance *)
let est_sad_valide (sac: sad) : bool =
  let rep = ref true in
  for i = 0 to (sac.n - 2) do
      if (sac.vi.(i) * sac.wi.(i + 1)) >= (sac.vi.(i + 1) * sac.wi.(i)) then ()
      else rep := false
  done;
  !rep

(* Valeur d'une solution *)
let valeur_sol (sac: sad) (s: solution) : int =
  let rep = ref 0 in
  for i = 0 to (sac.n - 1) do
    if s.(i) then
      rep := !rep + sac.vi.(i)
  done;
  !rep

(* Poids d'une solution *)
let poids_sol (sac: sad) (s: solution) : int =
  let rep = ref 0 in
  for i = 0 to (sac.n - 1) do
    if s.(i) then
      rep := !rep + sac.wi.(i)
  done;
  !rep

(* Test de validité d'un masque *)
let est_masque_valide (sac : sad) (m: masque) : bool =
  let rep = ref 0 in
  for i=0 to (sac.n - 1) do
    if m.(i) = Some(true) then
      rep := !rep + sac.vi.(i)
    else ()
  done;
  !rep < sac.p


(* 2. Par force brute *)

(* Addition binaire pour calculer le prochain masque *)
let next (m: masque) (s: solution) : unit =
  let i = ref 0 in
  while !i < (Array.length m) do
    if m.(!i) = None then
      begin
      if s.(!i) then
(*         if !i = (Array.length m - 1) then
          failwith("Addition max atteinte")
        else *)
          (s.(!i) <- false;
          i := !i + 1)
      else
        (s.(!i) <- true;
        i := Array.length m)
    end
    else i := !i +1
  done

(* Tests intermédiaires *)
let solution_test = [|false; false; true; false; false; false|]
let masque_test = [|None; None; None; None; None; None|]

(* Calcul d'une solution optimale *)
let brute_force (sac: sad) (m: masque) : (solution * int) option =
  if not (est_masque_valide sac m) then failwith("Masque invalide");
  let rep = ref None in
  let val0 = ref 0 in
  let cpt = ref sac.n in (* compte le nombre de possibilités à tester pour le tableau solution en fonction du masque *)
  let s0 = Array.init sac.n (fun x -> false) in (* au début on ne prend aucun objet sauf ceux que le masque impose *)
  let sol0 = ref s0 in
  for i = 0 to (sac.n - 1) do
    match m.(i) with
    |None    -> ()
    |Some(b) -> 
      if b then 
        begin
          (!sol0).(i) <- true;
          cpt := !cpt - 1
        end
      else 
        cpt := !cpt - 1
  done;
  let s = Array.copy (!sol0) in
  for i = 0 to int_of_float(2. ** float_of_int(sac.n - 1)) do
    if (valeur_sol sac s) > !val0 && (poids_sol sac s <= sac.p) then
      begin
        val0 := valeur_sol sac s;
        sol0 := Array.copy s
      end;
    next m s
  done;
  if !val0 <> 0 then rep := Some((!sol0) , (!val0));
  !rep


(* 3. Par programmation dynamique *)

let prog_dyn_tab (sac: sad) : int array array =
  let max x y = if x > y then x else y in
  let s = Array.make_matrix (sac.n + 1) (sac.p + 1) 0 in
  for i = sac.n - 1 downto 0 do
    for j = sac.p downto 0 do
      if sac.wi.(i) <= j then
        s.(i).(j) <- max s.(i + 1).(j) (sac.vi.(i) + s.(i + 1).(j - sac.wi.(i)))
      else
        s.(i).(j) <- s.(i + 1).(j)
      done;
  done;
  s

let prog_dyn (sac: sad) : solution * int =
  let s = prog_dyn_tab sac in
  let sol = Array.init sac.n (fun x -> false) in
  let valeur = s.(0).(sac.p) in
  for i = 0 to sac.n - 2 do
    if s.(i + 1).(sac.p - 1) <> s.(i).(sac.p - 1) then
      sol.(sac.n - i) <- true
  done;
  (sol , valeur)


(* 4. Algorithme glouton entier *)

let glouton_n (sac: sad) (m: masque) : (solution * int) option =
  if not (est_masque_valide sac m) then None
  else
  let sol = Array.init sac.n (fun i -> false) in
  let poids = ref 0 in
  for i = 0 to sac.n - 1 do
    match m.(i) with
    |None -> ()
    |Some(b) -> if b then poids := !poids + sac.wi.(i)
  done;
  for i = 0 to sac.n - 1 do
    match m.(i) with
    |None ->
      if (sac.wi.(i) + !poids) < sac.p then
        begin
          sol.(i) <- true;
          poids := !poids + sac.wi.(i)
        end
    |Some(b) -> sol.(i) <- b
  done;
  Some(sol , valeur_sol sac sol)


(* 6. Algorithme glouton fractionnaire *)

(* Poids d'une solution fractionnaire *)
let qpoids_sol (sac: sad) (s: qsolution) : Q.t =
  let rep = ref (Q.rat 0) in
  for i = 0 to (sac.n - 1) do
    let open Q in
    rep := (!rep + ((rat sac.wi.(i)) ** s.(i)))
  done;
  !rep

(* Valeur d'une solution fractionnaire *)
let qvaleur_sol (sac: sad) (s: qsolution) : Q.t =
  let rep = ref (Q.rat 0) in
  for i = 0 to (sac.n - 1) do
    let open Q in
    rep := (!rep + ((rat sac.vi.(i)) ** s.(i)))
  done;
  !rep

  (* Glouton fractionnaire *)
 let glouton_r (sac: sad) (m: masque) : (qsolution * Q.t) option =
  if not (est_masque_valide sac m) then None
  else
  let sol_n = glouton_n sac m in
  let sol_q = Array.make sac.n (Q.rat 0) in
  let b = ref true in
  let i = ref 0 in
  let rep = ref 0 in
  while !i < sac.n do
    begin
      match sol_n , m.(!i) with
      |None, None           -> ()
      |_, Some (a)          -> sol_q.(!i) <- (if a then Q.rat 1 else Q.rat 0)
      |Some (sol , v), None ->
        if !b then
          begin
          if sol.(!i) then
            sol_q.(!i) <- (Q.rat 1)
          else (b := false;
          rep := !i)
          end
    end;
    i := !i + 1
  done;
  print_int !rep;
  let poids_restant = Q.((Q.rat sac.p) - qpoids_sol sac sol_q) in
  if Q.signe poids_restant <> 1 then failwith("Poids négatif");
  let fraction = Q.(poids_restant // (Q.rat sac.wi.(!rep))) in
  if Q.((Q.rat 1) <= fraction) then
    sol_q.(!rep) <- Q.rat 1
  else
    sol_q.(!rep) <- fraction;
  Some (sol_q , qvaleur_sol sac sol_q)


(* 7. Algorithme de Branch-and-Bound *)

let impose_i (m: masque) (i: int) (b: bool) : masque =
  let copie = Array.copy m in
  copie.(i) <- Some(b); copie

let find_i_frac (qsol: qsolution) : int =
  let i = ref 0 in
  while !i < Array.length qsol - 1 && (Q.entier qsol.(!i)) do
    i := !i + 1
  done;
  if (Q.entier qsol.(!i)) then -1
  else
  !i
  
let branchement (sac: sad) (m: masque) (solq: qsolution) : masque * masque =
  let i = find_i_frac solq in
  let m1 = impose_i m i true in
  let m2 = impose_i m i false in
  (m1, m2)

let branch_and_bound (sac: sad) : solution * int =
  let meilleure_valeur = ref 0 in
  let meilleure_solution = ref (Array.make sac.n false) in
  let todo = Queue.create () in
  let m = Array.make sac.n None in
  for i = 0 to sac.n - 1 do 
    if est_masque_valide sac (impose_i m i true) then
      Queue.push (impose_i m i true) todo
  done;
  
  while not (Queue.is_empty todo) do 

    let i = Queue.pop todo in
    let solq_option = glouton_r sac i in
    let (solq, valq): qsolution * Q.t =
    match solq_option with
    |None            -> (Array.make sac.n (Q.rat 0), (0,0))
    |Some (sol , va) -> (sol , va)
    in

    if Q.((Q.rat !meilleure_valeur) < valq) then

      begin

        let soln_option = glouton_n sac i in
        let (soln, valn): solution * int =
          match soln_option with
          |None            -> (Array.make sac.n false, 0)
          |Some (sol , va) -> (sol , va)
        in

        if valn > !meilleure_valeur then

          begin

            meilleure_valeur := valn;
            meilleure_solution := soln;

          end;

        let valn2 = valn + 1 in

        if Q.((Q.rat valn2)  <= valq) then

          begin

          let j = find_i_frac solq in 
          if j = -1 then ()
          else
          let (sol1 , sol2) = branchement sac i solq in
          if est_masque_valide sac sol1 then
            Queue.push sol1 todo;
          if est_masque_valide sac sol2 then
            Queue.push sol2 todo;

          end;

      end;

  done;
  (!meilleure_solution, !meilleure_valeur)