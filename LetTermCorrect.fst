(* This example is transcribed from Adam Chlipala's
   Parametric Higher-order Abstract Syntax (ICFP 2008) paper.

   http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf
*)

module LetTermCorrect

open FStar.Tactics
open FStar.FunctionalExtensionality
open CPS


let eval_cont (#t0:cpstyp)
              (f:denote_cpstyp (CCont t0)) =
    fun x -> f x

let rec let_term_correct (#r1 #r2:cpstyp)
                         (t:cpsterm0 denote_cpstyp r1)
                         (e:denote_cpstyp r1 -> cpsterm0 denote_cpstyp r2)
                         (k:denote_cpstyp r2 -> bool)
                         : Lemma (ensures
                                     (denote_cpsterm0 r2
                                       (let_term denote_cpstyp t e) k) ==
                                      (denote_cpsterm0 r1 t
                                        (fun r -> denote_cpsterm0 r2 (e r) k)))
                                 (decreases t)
    = 
    let k' = (fun r -> denote_cpsterm0 r2 (e r) k) in
    match t with
    | Halt x -> ()
    | CApp x1 x2 -> ()
    | LetIn p f ->
            let_term_correct (f (denote_primop
                                 (let_prim denote_cpstyp p e) k)) e k;
            match p with
            | PApp #_ #_ #r0 g ->
              let g1 =
                fun (x:denote_cpstyp r0) ->
                  denote_cpsterm0 r2 (let_term denote_cpstyp (g x) e) k
              in
              let g2 =
                fun (x:denote_cpstyp r0) ->
                  denote_cpsterm0 r1 (g x) k'
              in
              assert_norm (forall(x:denote_cpstyp r0). (eval_cont (denote_primop
                                        (let_prim denote_cpstyp p e) k)) x ==
                              g1 x);
              let lem1 : (x:denote_cpstyp r0) -> Lemma (g1 x == g2 x) =
                fun x ->
                  assert ((g x) << p);
                  assert (p << t);
                  let_term_correct (g x) e k;
                  ()
              in
              FStar.Classical.forall_intro lem1;
              assert (feq
                       (denote_primop (let_prim denote_cpstyp (PApp g) e) k)
                       (denote_primop (PApp g) k'));
              assert (
                (on_domain
                  (denote_cpstyp r0)
                  (denote_primop (let_prim denote_cpstyp (PApp g) e) k)) ==
                (on_domain
                  (denote_cpstyp r0)
                  (denote_primop (PApp g) k')));
              assert (
                (on_domain
                  (denote_cpstyp r0)
                  (denote_primop (let_prim denote_cpstyp (PApp g) e) k)) ==
                (denote_primop (let_prim denote_cpstyp (PApp g) e) k))
                by (norm [delta_only[`%let_prim;`%denote_primop]; zeta; iota]);
              assert (
               (on_domain
                  (denote_cpstyp r0)
                  (denote_primop (PApp g) k')) ==
               (denote_primop (PApp g) k'))
               by (norm [delta_only[`%let_prim;`%denote_primop]; zeta; iota]);
              assert (
                (denote_primop (let_prim denote_cpstyp (PApp g) e) k) ==
                (denote_primop (PApp g) k'));
              assert
                (denote_cpsterm0 r2
                  (let_term denote_cpstyp (LetIn (PApp g) f) e) k ==
                 denote_cpsterm0 r2
                   (let_term
                     denote_cpstyp
                     (f (denote_primop (let_prim denote_cpstyp (PApp g) e) k))
                     e)
                   k)
               by (norm [delta_only [`%let_term]]);
              assert (
                denote_cpsterm0
                  r2 (let_term denote_cpstyp (LetIn (PApp g) f) e) k ==
                denote_cpsterm0 r2 (let_term denote_cpstyp (f (denote_primop (PApp g) k')) e) k)
                by (
                  norm [zeta;
                        delta_only[`%let_term;`%denote_cpsterm0];
                        iota;
                        weak]);
              let lem3 () : Lemma (
                  (denote_cpsterm0 r1 (LetIn (PApp g) f) k') ==
                  (denote_cpsterm0
                    r2
                    (let_term
                      denote_cpstyp (f (denote_primop (PApp g) k')) e) k)) =
                let_term_correct (f (denote_primop (PApp g) k')) e k;
                ()
              in
              assert (
                 (denote_cpsterm0 r1 (LetIn (PApp g) f) k') ==
                 (denote_cpsterm0 r2 (let_term denote_cpstyp (LetIn (PApp g) f) e) k))
    | _ -> ();
    ()
    
              


