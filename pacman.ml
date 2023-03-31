(**
  * Projet Ocaml Pac Man 
  * On essaie de résoudre un labyrinthe parfait en tant que pacman un point bleu
  * pendant qu'un fantome, en rouge, va essayer de nous bloquer. 
  *
  * Van Der Donckt 
  *)

(* #load "graphics.cma";; *)

(**
  *  Module UF 
  *)

module UF = 
struct
  type noeud = {
    mutable parent:int;
    mutable rang:int
  }
  type t = noeud array

  (* type arbre = Racine of cell | Noeud of cell *)
  
  let create n = Array.init n ( fun i -> ({ parent = i; rang = 0}))

  let rec find uf indice = match uf.(indice) with
    | cell when cell.parent = indice -> cell
    | cell -> find uf cell.parent
           
  let union uf n m =
    let racine_n = find uf n in
    let racine_m = find uf m in
    match racine_n, racine_m with
    | r1, r2 when r1 = r2 -> () 
    | r1, r2 when r1.rang < r2.rang -> racine_n.parent <- racine_m.parent
    | _ , _ ->
      racine_m.parent <- racine_n.parent;
      if racine_n.rang = racine_m.rang then
        racine_m.rang <- racine_m.rang + 1 
end 

(** 
  * LABYRINTHE
  *)

let mur_au_hasard l h =
  let n = Random.int (( l - 1 ) * h + l * ( h - 1 )) in (* [0 ; borne = nombre total de mur [ *)
  if n < ( l - 1 ) * h then (* Les (borne/2) murs verticaux *)
    ( 1, n mod ( l - 1 ), n / ( l - 1 ))
  else (* Les (bornes/2) murs horizontaux *)
    let n2 = n - ( l - 1 ) * h in
    ( 0, n2 mod l, n2 / l ) 

(* Renvoie le couple des numéros des deux cases séparées par le mur (d,x,y) *)
let case_adjacentes l h (d,x,y) =
  let case1 = y * l + x in
  ( case1 , case1 + d + l - d * l )

let generate_lab l h =
  (* On ne presente que les murs intérieurs, le pourtour est tracé indépendamment*)
  let mur_present = Array.init 2 (fun d ->
      Array.init (h - 1 + d) (fun _ -> (* Murs horizontaux *)
          Array.init (l - d) (fun _ -> true) (* Murs verticaux *)
      )
  ) in
  
  let voisines = Array.make (l*h) [] in

  let uf = UF.create ( l * h ) in
  let k = ref 0 in
  
  while !k < l * h - 1 do (* Pour chaque case de UF *)
    let m = mur_au_hasard l h in 
    let ( i, j ) = case_adjacentes l h m in (* i et j 2 cases *)

    if UF.find uf i <> UF.find uf j then
    begin
      UF.union uf i j ;
      let ( d, x, y ) = m in mur_present.(d).(y).(x) <- false;
      
      voisines.(i) <- (j :: voisines.(i));
      voisines.(j) <- (i :: voisines.(j));

      k := !k + 1
    end
  done; 
  ( mur_present, voisines )

type point = { abs : int ; ord : int }

(* Trace le tour du labyrinthe en laissant ouvert l'entrée et la sortie *)
let trace_pourtour upleftx uplefty taille_case h l =
  let upright = {
    abs = upleftx + taille_case * l ;
    ord = uplefty
  } in
  let downright = {
    abs = upright.abs ;
    ord = upright.ord - taille_case * h
  } in
  let downleft = {
    abs = downright.abs - taille_case * l ;
    ord = downright.ord ;
  } in
  let rec iter num_cote = function
    | [] -> Graphics.lineto upleftx (uplefty - taille_case)
    | hd :: tl when num_cote = 2 ->
      Graphics.lineto hd.abs (hd.ord + taille_case) ;
      Graphics.moveto hd.abs hd.ord ;
      iter (num_cote + 1) tl
    | hd :: tl -> Graphics.lineto hd.abs hd.ord ; iter (num_cote + 1) tl
  in
  Graphics.moveto upleftx uplefty ;
  iter 1 [ upright ; downright ; downleft ]

(* Trace un mur en fonction de ses coordonnes d x y *)
let trace_mur upleftx uplefty taille_case (d,x,y) =
  let base_trace = { (* Point de depart de notre segment *)
    abs = upleftx + (x + 1) * taille_case ;
    ord = uplefty - (y + 1) * taille_case 
  } in
  Graphics.moveto base_trace.abs base_trace.ord ;
  if d = 1 then
    Graphics.lineto base_trace.abs (base_trace.ord + taille_case)
  else
    Graphics.lineto (base_trace.abs - taille_case) base_trace.ord 

let trace_lab upleftx uplefty taille_case l h mur_present = 
  trace_pourtour upleftx uplefty taille_case h l;
  (* On parcourt chaque element de nos 2 matrices *)
  for d = 0 to 1 do 
    for y = 0 to h - 2 + d do 
      for x = 0 to l - 1 - d do
        if mur_present.(d).(y).(x) then
          trace_mur upleftx uplefty taille_case (d,x,y)
      done 
    done
  done

(**
  * PERSONNAGE 
  *
  *)

(**
  * Définition des personnages 
  * on aurait aussi pus faire des class et ajouter les méthodes qui 
  * sont propre a chaque personnage dans des sous class correspondantes ?
  *)
type personnage = {
  mutable case: int;
  couleur: Graphics.color;
}

let pacman = {
  case = 0;
  couleur = Graphics.blue;
}

let fantome = {
  case = 0 ; (* Serra initialisé quand on aurra acces a l *)
  couleur = Graphics.red
}

(**
  * On defini une variable globale pour arreter les 2 boucles quand 
  * un des deux personnages a perdu. 
  *)
let perdu = ref false

(* Faire le dessin pour s'en convaincre *)
let coordonnees_mur l case1 case2 = 
  let case_ref = 
    if case2 < case1 then case2
    else case1 
  in ( case_ref mod l, case_ref / l )

(**
  * Renvoie la prochaine case ainsi que la direction du mur 
  * qui sépare la case actuelle et la prochaine case 
  *)
let analyse_deplacement l touche_presse = match touche_presse with
  | 's' -> ( 1, pacman.case + 1 ) (* droite *)
  | 'a' -> ( 1, pacman.case - 1 ) (* gauche *)
  | 'w' -> ( 0, pacman.case - l ) (* haut *)
  | 'z' -> ( 0, pacman.case + l ) (* bas *)
  | _ -> ( 0, pacman.case )
 
(* On vérifie que le pacman peut se déplacer entre 2 cases *)
let autorisation_dplcmt l h mur_present ( d, prochaine_case ) = 
  let ( x, y ) = coordonnees_mur l pacman.case prochaine_case in 

  try 
    if mur_present.(d).(y).(x) then false 
    else true 
  with 
  | Invalid_argument str -> false

(* Cette fonction sert pour mettre a jour la représentation des deux personnages sur le dessin *)
let mise_a_jour_perso l const_x const_y taille_case rayon personnage prochaine_case = 
  (* On efface le personnage de sa position actuelle *)
  let x = const_x + ( personnage.case mod l ) * taille_case in 
  let y = const_y - ( personnage.case / l ) * taille_case in 
  Graphics.set_color Graphics.background;
  Graphics.fill_circle x y rayon;

  (* On dessine le personnage a sa nouvelle position *)
  let x = const_x + ( prochaine_case mod l ) * taille_case in 
  let y = const_y - ( prochaine_case / l ) * taille_case in 
  Graphics.set_color personnage.couleur;
  Graphics.fill_circle x y rayon;
  Graphics.set_color Graphics.foreground;
  personnage.case <- prochaine_case

(* On regarde si 2 cases sont relié par un chemin *)
let rec est_relie src dst evite voisines = 
  if src = dst then true
  else let rec iter l = match l with 
  | [] -> false 
  | hd :: tl when hd = evite -> iter tl
  | hd :: tl -> iter tl || est_relie hd dst src voisines 
  in iter voisines.(src)

(* Calcule le numero de la prochaine case du fantome *)
let prochaine_case_fantome l h voisines = 
  let rec iter l_voisines = match l_voisines with 
  | [] -> fantome.case 
  | hd :: tl -> 
    if est_relie hd pacman.case fantome.case voisines then hd
    else iter tl
  in iter voisines.(fantome.case)

(* On creer et execute chacune des deux boucles infinis, fonction principale du programme *)
let jeu l h upleftx uplefty taille_case = 
  (* on definie ces variables pour que ça soit plus clair dans mis_a_jour_perso *)
  let const_x = upleftx + taille_case / 2 in 
  let const_y = uplefty - taille_case / 2 in 
  let rayon = taille_case / 2 - 2 in 

  (* On genere le labyrinthe et on le trace *)
  let ( mur_present, voisines ) = generate_lab l h in 
  let _ = trace_lab upleftx uplefty taille_case l h mur_present in 

  let rec boucle_fantome () = 
    Unix.sleep 2; 
    if !perdu then ()
    else begin 
      mise_a_jour_perso l const_x const_y taille_case rayon fantome (prochaine_case_fantome l h voisines );
      (* On test si le fantome a atteint le pacman *)
      if pacman.case = fantome.case || fantome.case = l * h - 1 then begin
        Graphics.moveto 10 10 ;
        Graphics.draw_string "PERDU !";
        perdu := true ;
      end;
      boucle_fantome ()
    end;
  in

  let rec iter frappe_disponible = 
    (* Si on a perdu on ne peut pas se deplacer *)
    if not !perdu && frappe_disponible then begin match Graphics.read_key () with 
      | 'q' -> Graphics.close_graph ()
      | kp -> let ( d, prochaine_case ) = analyse_deplacement l kp in
        if autorisation_dplcmt l h mur_present ( d , prochaine_case ) then begin
            mise_a_jour_perso l const_x const_y taille_case rayon pacman prochaine_case;
            (* On teste si le pacman a atteint son but *)
            if prochaine_case = ( l * h - 1 ) then begin
              Graphics.moveto 10 10 ;
              Graphics.draw_string "GAGNE !";
              perdu := true 
            end 
        end 
        else 
          Graphics.sound 1000 1000;

        (* On teste si le pacman a atteint le fantome *)
        if pacman.case = fantome.case then begin
          Graphics.moveto 10 10 ;
          Graphics.draw_string "PERDU !";
          perdu := true ;
        end;
    end;
    
    (* Si personne n'a pas perdu on peut continuer *)
    if not !perdu then iter (Graphics.key_pressed ())
  in 
  perdu := false; (* On commence la partie on ne peut pas avoir perdu *)
  (**
    * Initialisation des personnages
    * On est obligé de mettre fantome avant pacman 
    * a cause de la maniere dont et fait mise_a_jour_personnage 
    * et parce qu'on initialise fantome a 0 lors de sa definition  
    *)
  mise_a_jour_perso l const_x const_y taille_case rayon fantome (l-1);
  mise_a_jour_perso l const_x const_y taille_case rayon pacman 0;

  ignore (Thread.create boucle_fantome ()); (* se termine quand boucle_fantome retourne *)
  (** 
    * On lance la boucle iter a la fin des autres instructions parce que 
    * sinon elles seront executés seulement a la sortie de la récusrion 
    * de iter 
    *)
  iter (Graphics.key_pressed ())  

(* On intialise la fenetre Graphics *)
let () = Graphics.open_graph " 1000*1000";;
let () = Graphics.set_window_title "P Hack MAN";;

(* On définie change la graine pour obtenir mur au hasard *)
let () = Random.self_init ()

(* On lance une partie *)
let _ = jeu 10 11 100 350 20

(* A la fin de la partie on attend que le joueur tappe une touche pour fermer la fenetre *)
let _ = Graphics.read_key ()