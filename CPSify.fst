(* This example is transcribed from Adam Chlipala's
   Parametric Higher-order Abstract Syntax (ICFP 2008) paper.

   http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf
*)
module CPSify

include FStar.List.Tot
include FStar.Tactics
include FStar.FunctionalExtensionality
include Term
include CPS

#push-options "--fuel 3"

let rec typ_translate (t:typ) : cpstyp =
  match t with
  | Bool -> CBool
  | Arrow t1 t2 -> CCont (CTimes (typ_translate t1) (CCont (typ_translate t2)))

let rec term_translate0 (v:cpstyp -> Type)
                    (#t0:typ)
                    (t:term0 (fun t -> v (typ_translate t)) t0):
                    Tot (cpsterm0 v (typ_translate t0))
                        (decreases t)
    = match t with
    | Var x -> Halt x
    | TT -> LetIn PT Halt
    | FF -> LetIn PF Halt
    | App #_ #t1 #t2 e1 e2 ->
      let_term v (term_translate0 v e1) 
        (fun f -> let_term v (term_translate0 v e2)
          (fun x -> 
            LetIn (PApp #_ #_  #(typ_translate t2) Halt) (fun x0 ->
              LetIn (PPair #_ #_
                           #(typ_translate t1)
                           #(CCont (typ_translate t2)) x x0) (fun x1 ->
                CApp #_ #_
                #(CTimes (typ_translate t1) (CCont (typ_translate t2)))
                f x1))))
    | Lam #_ #t1 #t2 f ->
      LetIn #_ #_ #(CCont (CTimes (typ_translate t1)
                                  (CCont (typ_translate t2))))
        (PApp #_ #_ #(CTimes (typ_translate t1)
                             (CCont (typ_translate t2)))
              (fun (p:v (CTimes (typ_translate t1) (CCont (typ_translate t2)))) ->
          (LetIn #_ #_ #(typ_translate t1)
            (PProj1 #v
                    #_ 
                                                 
                    #(typ_translate t1)
                    #(CCont (typ_translate t2)) p) (fun x ->
            (LetIn (PProj2 #v #_ #(typ_translate t1)
                           #(CCont (typ_translate t2)) p) (fun k ->
              let_term v (term_translate0 v (f x)) (fun r -> CApp k r)))))))
        Halt

let term_translate (#t:typ) (e:term t) : cpsterm (typ_translate t) =
  fun v -> term_translate0 v (e (fun x -> v (typ_translate x)))

let denote_typ_trans = fun (t:typ) -> denote_cpstyp (typ_translate t)

let denote_term_trans0
  (#t0:typ)
  (t:term0 (fun t -> denote_typ_trans t) t0)
  (k:denote_typ_trans t0 -> bool)
  : bool
  = denote_cpsterm0
      (typ_translate t0)
      (term_translate0 denote_cpstyp t)
      k



