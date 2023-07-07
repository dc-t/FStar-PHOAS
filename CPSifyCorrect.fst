(* This example is transcribed from Adam Chlipala's
   Parametric Higher-order Abstract Syntax (ICFP 2008) paper.

   http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf
*)
module CPSifyCorrect

include FStar.List.Tot
include FStar.Tactics
include FStar.FunctionalExtensionality
include Term
include CPS
include LetTermCorrect
include CPSify

val unwrap_trans (#t1 #t2:typ)
                 (f:denote_typ (Arrow t1 t2))
                 (x:denote_typ t1)
                 : denote_typ t2
let unwrap_trans f x =
  f x

val unwrap_trans_cps (#t1 #t2:cpstyp)
                     (f:denote_cpstyp (CCont (CTimes t1 t2)))
                     (x:denote_cpstyp t1)
                     (k:denote_cpstyp t2)
                     : bool
                     
let unwrap_trans_cps f x k =
  f (x, k)

let rec memPc (#a:Type)
          (p:a)
          (l:list a)
          : Type
    = match l with
    | [] -> False
    | h :: t -> (either (equals p h) (memPc p t))

let squash_eq (#a:Type) (x y:a) (r:equals x y) : Lemma (x == y)
  = FStar.Squash.return_squash r

let rec denote_typ_equiv (#t:typ)
                         (e1:denote_typ t)
                         (e2:denote_typ_trans t)
                         : Type =
    match t with 
    | Bool -> equals e1 e2
    | Arrow t1 t2 ->
      x1:(denote_typ t1) ->
      x2:(denote_typ_trans t1) ->
      hx:(denote_typ_equiv x1 x2) ->
      (r:(denote_typ_trans t2){
          forall(k:denote_typ_trans t2 -> bool).
            (unwrap_trans_cps
              #(typ_translate t1)
              #(CCont (typ_translate t2))
              e2 x2 k) == k r}
      & (denote_typ_equiv #t2 (unwrap_trans e1 x1) r))

type var_pair (v1 v2: typ -> Type) = t:typ & v1 t & v2 t

noeq
type deduct (#v1 #v2: typ -> Type) : g:(list (var_pair v1 v2)) ->            
              t:typ ->
              (e1:term0 v1 t) ->
              (e2:term0 v2 t) ->
              Type =
     | DVar : h:list (var_pair v1 v2) -> p:(var_pair v1 v2)->
              deduct (p :: h) (Mkdtuple3?._1 p)
                       (Var (Mkdtuple3?._2 p)) (Var (Mkdtuple3?._3 p))
     | DTrue : #h:list (var_pair v1 v2) ->
               deduct h Bool TT TT
     | DFalse : #h:list (var_pair v1 v2) ->
               deduct h Bool FF FF
     | DApp : #h:list (var_pair v1 v2) ->
              t1:typ ->
              t2:typ ->
              f1:term0 v1 (Arrow t1 t2) ->
              f2:term0 v2 (Arrow t1 t2) ->
              a1:term0 v1 t1 ->
              a2:term0 v2 t1 ->
              deduct h (Arrow t1 t2) f1 f2 ->
              deduct h t1 a1 a2 ->
              deduct h t2 (App f1 a1) (App f2 a2)
     | DLam : #h:list (var_pair v1 v2)->
              t1:typ ->
              t2:typ ->
              f1:(v1 t1 -> term0 v1 t2) ->
              f2:(v2 t1 -> term0 v2 t2) ->
              (x1:v1 t1 -> x2:v2 t1 ->
              deduct ((|t1, x1, x2|) :: h) t2 (f1 x1) (f2 x2)) ->
              deduct h (Arrow t1 t2) (Lam f1) (Lam f2)
              
              

type well_formed (#t:typ) (e:term t) =
  v1:(typ -> Type) -> v2:(typ -> Type) -> (deduct [] t (e v1) (e v2))


let rec correctness_lemma
  (h: list (var_pair denote_typ denote_typ_trans))
  (h1:(p:(var_pair denote_typ denote_typ_trans) ->
         (memPc p h) ->
         (denote_typ_equiv
           #(Mkdtuple3?._1 p)
            (Mkdtuple3?._2 p)
            (Mkdtuple3?._3 p))))
  (t:typ)
  (e1:term0 denote_typ t)
  (e2:term0 denote_typ_trans t)
  (d: deduct h t e1 e2)
  : Tot (r:(denote_typ_trans t){
             forall(k:denote_typ_trans t -> bool).
               (denote_term_trans0 e2 k == k r)} &
        (denote_typ_equiv (denote_term0 e1) r))
    (decreases d)
  = match d with
  | DVar h0 p ->
    let x1, x2 = Mkdtuple3?._2 p, Mkdtuple3?._3 p in
    assert (
      (forall(k:denote_typ_trans t -> bool).
        (denote_term_trans0 e2 k == k x2)))
    by (
      let k = forall_intro () in
      norm [
        delta_only
          [`%denote_term_trans0;
           `%denote_cpsterm0;
           `%term_translate0];
        zeta;
        iota]);
    assert (p::h0 == h);
    let mp : memPc p (p::h0) = Inl Refl in
    (|x2, (h1 p mp)|)
  | DTrue -> 
    assert (e2 == TT #denote_typ_trans);
    assert_norm (forall(k:denote_typ_trans t -> bool).
                           (denote_cpsterm0
                             (typ_translate t)
                             (term_translate0
                               denote_cpstyp (TT #denote_typ_trans))
                             k ==
                           k true));
    assert (forall(k:denote_typ_trans t -> bool).
                           (denote_cpsterm0
                             (typ_translate t)
                             (term_translate0 denote_cpstyp e2)
                             k
                           == k true));
    (|true, (Refl #bool #true)|)
  | DFalse ->
    assert (e2 == FF #denote_typ_trans);
    assert_norm (forall(k:denote_typ_trans t -> bool).
                           (denote_cpsterm0
                             (typ_translate t)
                             (term_translate0
                               denote_cpstyp (FF #denote_typ_trans))
                             k ==
                           k false));
    assert (forall(k:denote_typ_trans t -> bool).
                           (denote_cpsterm0
                             (typ_translate t)
                             (term_translate0 denote_cpstyp e2)
                             k
                           == k false));
    (|false, (Refl #bool #false)|)
  | DApp t1 t2 f1 f2 a1 a2 df da ->
    let (ra : (denote_typ_trans t1){
             forall(k:denote_typ_trans t1 -> bool).
               (denote_term_trans0 a2 k == k ra)}) =
               dfst (correctness_lemma h h1 t1 a1 a2 da)
    in
    let ha =  dsnd (correctness_lemma h h1 t1 a1 a2 da) in
    let (rf : (denote_typ_trans (Arrow t1 t2)){
             forall(k:denote_typ_trans (Arrow t1 t2) -> bool).
               (denote_term_trans0 f2 k == k rf)})
      = dfst (correctness_lemma h h1 (Arrow t1 t2) f1 f2 df)
    in
    let hf = dsnd (correctness_lemma h h1 (Arrow t1 t2) f1 f2 df) in
    let r0 : denote_typ_trans t2 = dfst (hf (denote_term0 a1) ra ha) in
    let hr = dsnd (hf (denote_term0 a1) ra ha) in
    let lem1 k : Lemma (denote_term_trans0 (App f2 a2) k == k r0) =
      let kx x f =
        denote_cpsterm0
                  (typ_translate t2)
                  (CApp #_ #_
                  #(CTimes (typ_translate t1) (CCont (typ_translate t2))) f
                    (x, (on_domain (denote_typ_trans t2) (fun r -> k r))))
                  k
      in
      let kf f = denote_term_trans0  a2 (fun x -> kx x f) in
      let t0 = denote_term_trans0 f2 kf in
      assert (
        denote_term_trans0 (App f2 a2) k == t0)
      by (
        norm [
          delta_only [`%denote_term_trans0;
                      `%term_translate0];
          zeta;
          iota];
        l_to_r [`let_term_correct];
        mapply (`denote_cpsterm0_extensional);
        norm [delta_only [`%feq]];
        l_to_r [`let_term_correct];
        let x = forall_intro () in
        mapply (`denote_cpsterm0_extensional);
        compute ());
      assert (t0 == rf (ra, k));
      assert (k r0 == unwrap_trans_cps rf ra k);
      ()
    in
    FStar.Classical.forall_intro lem1;
    (|r0, hr|)
  | DLam t1 t2 f1 f2 hyp ->
    let r0 =
      on_domain
        ((denote_typ_trans t1) * ((denote_typ_trans t2) -> bool))
        (fun p ->
          (denote_term_trans0
            (f2 (fst p))
            (on_domain (denote_typ_trans t2) (fun x -> snd p x))))
    in
    let lem1 k : Lemma (denote_term_trans0 (Lam f2) k == k r0) =
      let t0 =
        (on_domain ((denote_typ_trans t1) * ((denote_typ_trans t2) -> bool))
          (fun x ->
            denote_cpsterm0 _
              (let_term
                denote_cpstyp
                (term_translate0 denote_cpstyp (f2 (fst x)))
                (fun r' -> (CApp #denote_cpstyp (snd x) r')))
              k))
      in
      assert (
        denote_term_trans0 (Lam f2) k == k t0)
      by (
         norm [
           delta_only
             [
             `%denote_cpstyp;
             `%denote_typ_trans;
             `%typ_translate;
             `%denote_term_trans0;
             `%term_translate0;
             `%denote_cpsterm0;
             `%denote_primop];
         iota;
         zeta];
         trefl());
      assert (
        feq #((denote_typ_trans t1) * ((denote_typ_trans t2) -> bool)) t0 r0)
      by (
        norm [delta_only[`%feq]];
        let x = forall_intro () in
        l_to_r [`let_term_correct];
        norm [delta_only[`%denote_term_trans0]];
        mapply (`denote_cpsterm0_extensional));
      extensionality
        ((denote_typ_trans t1) * ((denote_typ_trans t2) -> bool)) _ t0 r0;
      ()
    in
    FStar.Classical.forall_intro lem1;
    assert_norm (
      denote_typ_trans (Arrow t1 t2) ==
      (((denote_typ_trans t1) * ((denote_typ_trans t2) -> bool)) -> bool));
      let hy (x1:denote_typ t1)
             (x2:denote_typ_trans t1)
             (hx:denote_typ_equiv x1 x2)
             (p:var_pair denote_typ denote_typ_trans)
             (mp: memPc p ((|t1, x1, x2|):: h))
             : denote_typ_equiv
                 #(Mkdtuple3?._1 p)
                 (Mkdtuple3?._2 p)
                 (Mkdtuple3?._3 p)
          = match (mp <: (either (equals p (|t1, x1, x2|)) (memPc p h))) with
          | Inl r ->
            (squash_eq p (|t1, x1, x2|) r; hx)
          | Inr m -> h1 p m
          | _ -> false_elim ()
      in
      assert (
        forall k (x2:denote_typ_trans t1).
          unwrap_trans_cps #(typ_translate t1) #(CCont (typ_translate t2))
          r0 x2 k ==
          denote_term_trans0 (f2 x2) k)
      by (
        norm [delta_only[`%denote_term_trans0; `%unwrap_trans_cps];
              zeta;
              iota];
        let xs = forall_intros () in
        mapply (`denote_cpsterm0_extensional));
      let lem2 : denote_typ_equiv (denote_term0 (Lam f1)) r0 = 
        fun (x1:denote_typ t1) 
          (x2:denote_typ_trans t1)
          (hx: denote_typ_equiv x1 x2)->
          correctness_lemma
            ((|t1, x1, x2|)::h)
            (hy x1 x2 hx)
            t2
            (f1 x1)
            (f2 x2)
            (hyp x1 x2)
      in
      (|r0, lem2|)
   
val semantic_correctness
  (t:typ)
  (e:(term t))
  (h:well_formed e)
  : Tot (r:(denote_typ_trans t){
      forall(k:denote_typ_trans t -> bool).
          (denote_cpsterm (term_translate e) k == k r)} &
        (denote_typ_equiv (denote_term e) r))

let semantic_correctness t e h =
  assert (term_translate0 denote_cpstyp (e denote_typ_trans) ==
         (term_translate e) denote_cpstyp)
    by (norm [delta_only[`%term_translate;`%denote_typ_trans]]);
  correctness_lemma []
                    (fun p -> false_elim)
                    t
                    (e denote_typ)
                    (e denote_typ_trans)
                    (h denote_typ denote_typ_trans)
