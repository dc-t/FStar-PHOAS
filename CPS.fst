(* This example is transcribed from Adam Chlipala's
   Parametric Higher-order Abstract Syntax (ICFP 2008) paper.

   http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf
*)

module CPS
open FStar.Tactics
open FStar.FunctionalExtensionality

type cpstyp =
  | CBool
  | CUnit
  | CCont : cpstyp -> cpstyp
  | CTimes : cpstyp -> cpstyp -> cpstyp

noeq
type primop (v:cpstyp -> Type) (r:cpstyp) : cpstyp -> Type =
  | PVar : #t:cpstyp -> v t -> primop v r t
  | PT : primop v r CBool
  | PF : primop v r CBool
  | PApp : #t1:cpstyp ->
           f:(v t1 -> cpsterm0 v r) -> primop v r (CCont t1)
  | PPair : #t1:cpstyp -> #t2:cpstyp ->
            x1:v t1 -> x2:v t2 ->
            primop v r (CTimes t1 t2)
  | PProj1 : #t1:cpstyp -> #t2:cpstyp ->
             x:v (CTimes t1 t2) ->
             primop v r t1
  | PProj2 : #t1:cpstyp -> #t2:cpstyp ->
             x:v (CTimes t1 t2) ->
             primop v r t2
and cpsterm0 (v:cpstyp -> Type) (r:cpstyp) : Type =
  | Halt :  x:v r -> cpsterm0 v r 
  | CApp : #t:cpstyp ->
           x1:v (CCont t) -> x2: v t ->
           cpsterm0 v r
  | LetIn : #t:cpstyp ->
            p:primop v r t -> f:(v t -> cpsterm0 v r) ->
            cpsterm0 v r
    
type cpsterm (t:cpstyp) = v:(cpstyp -> Type) -> cpsterm0 v t


let rec denote_cpstyp (t:cpstyp) : Type =
  match t with
  | CBool -> bool
  | CUnit -> unit
  | CCont t0 ->
    (denote_cpstyp t0) -> bool
  | CTimes t1 t2 -> (denote_cpstyp t1) * (denote_cpstyp t2)



let ccont_lem (t:cpstyp) :
  Lemma (denote_cpstyp (CCont t) == (_:denote_cpstyp t -> bool)) =
  assert (denote_cpstyp (CCont t) == (_:denote_cpstyp t -> bool))
  by (let t = forall_intro in compute())

let rec denote_cpsterm0 (r:cpstyp)
                        (t:cpsterm0 denote_cpstyp r)
                        (k:denote_cpstyp r -> bool)
                        : Tot (bool)
                              (decreases t) =
    match t with
    | Halt x -> k x
    | CApp x1 x2 -> x1 x2
    | LetIn p e -> denote_cpsterm0 r (e (denote_primop p k)) k
    
and denote_primop (#r #t:cpstyp)
                  (p:primop denote_cpstyp r t)
                  (k:denote_cpstyp r -> bool)
                  : Tot (denote_cpstyp t)
                        (decreases p)=
    match p with
    | PVar x -> x
    | PT -> true
    | PF -> false
    | PApp #_ #_ #t0 f ->
      on_domain
        (denote_cpstyp t0)
        (fun (x:denote_cpstyp t0) -> denote_cpsterm0 r (f x) k)
    | PPair x1 x2 -> (x1, x2)
    | PProj1 p -> fst p
    | PProj2 p -> snd p

let rec denote_cpsterm0_extensional
    (#r:cpstyp)
    (t:cpsterm0 denote_cpstyp r)
    (k1: (denote_cpstyp r) -> bool)
    (k2:((denote_cpstyp r) -> bool))
    : Lemma (requires feq k1 k2)
            (ensures denote_cpsterm0 r t k1 == denote_cpsterm0 r t k2)
            (decreases t)
    = match t with
    | Halt _ -> ()
    | CApp _ _ -> ()
    | LetIn p e ->
      denote_primop_extensional p k1 k2;
      denote_cpsterm0_extensional (e (denote_primop p k1)) k1 k2;
      denote_cpsterm0_extensional (e (denote_primop p k2)) k1 k2;
      ()
and denote_primop_extensional
  (#r #t:cpstyp)
  (p:primop denote_cpstyp r t)
  (k1: (denote_cpstyp r) -> bool)
  (k2:((denote_cpstyp r) -> bool))
  : Lemma
    (requires feq k1 k2)
    (ensures denote_primop p k1 == denote_primop p k2)
    (decreases p)
  = match p with
  | PApp #_ #_ #t0 f ->
    let lem1 x
    : Lemma (ensures denote_cpsterm0 r (f x) k1 == denote_cpsterm0 r (f x) k2)
    = denote_cpsterm0_extensional (f x) k1 k2;
      ()
    in
    FStar.Classical.forall_intro lem1;
    assert (
      feq #(denote_cpstyp t0)
        (fun x -> denote_cpsterm0 r (f x) k1)
        (fun x -> denote_cpsterm0 r (f x) k2));
    assert (
      denote_primop (PApp f) k1 == denote_primop (PApp f) k2)
    by (
      norm [delta_only[`%denote_primop]; zeta; iota]);
    ()
  | _ -> ()
    
  
let denote_cpsterm (#t0:cpstyp) (t:cpsterm t0) (k:denote_cpstyp t0 -> bool)
                   : bool
    = denote_cpsterm0 t0 (t denote_cpstyp) k


let rec let_term (v:cpstyp -> Type)
             (#t1 #t2:cpstyp)
             (t:cpsterm0 v t1)
             (e:v t1 -> cpsterm0 v t2)
             : Tot (cpsterm0 v t2)
               (decreases t)=
    match t with
    | Halt x -> e x
    | CApp x1 x2 -> CApp x1 x2
    | LetIn #_ #_ #t p f ->
      LetIn (let_prim v p e) (on_domain (v t) (fun x -> let_term v (f x) e))
and let_prim (v:cpstyp -> Type)
             (#t1 #t2 #t : cpstyp)
             (p:primop v t1 t)
             (e: v t1 -> cpsterm0 v t2)
             : Tot (primop v t2 t)
               (decreases p)=
    match p with
    | PApp #_ #_ #t0 f -> PApp #_ #_ #t0 (on_domain (v t0) (fun (x:v t0) -> let_term v (f x) e))
    | PVar x -> PVar x
    | PT -> PT
    | PF -> PF
    | PPair x1 x2 -> PPair x1 x2
    | PProj1 x -> PProj1 x
    | PProj2 x -> PProj2 x


    
