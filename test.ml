(* DEFINITION DES TYPES  *)

type player = J1 | J2
type cell = Pion of player * int | Vide
type grid = cell array array

(* DEFINITION DES FONCTIONS  *)

let copier_matrice (matrice : grid) =
  let nb_lignes = Array.length matrice in
  let nb_colonnes = Array.length matrice.(0) in
  let nouvelle_matrice = Array.make_matrix nb_lignes nb_colonnes Vide (* initialiser avec des valeurs par défaut *) in
  for i = 0 to nb_lignes - 1 do
    for j = 0 to nb_colonnes - 1 do
      nouvelle_matrice.(i).(j) <- matrice.(i).(j)
    done
  done;
  nouvelle_matrice


let joue (g : grid)(c : int * int)(p : player)(numero : int) : grid =
  let (i,j) = c in 
  if g.(i).(j)= Vide then
    let copie = copier_matrice g in
    copie.(i).(j) <- Pion(p,numero); copie
  else
    failwith("Case occupée")

let trouve_dernier_coup (g : grid): int*int =
  let max = ref 0 in
  let argmax = ref (0,0) in
  for i = 0 to 8 do
    for j = 0 to 8 do
      match g.(i).(j) with
      |Vide      -> ()
      |Pion(p,q) -> if q > (!max) then (argmax := (i,j); max := q)
    done
  done;
  !argmax

(* TESTS  *)

let grille_test = Array.make_matrix 9 9 Vide 
let () = 
  grille_test.(5).(6) <- Pion(J1 , 8)