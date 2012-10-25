module ListLike where

open import Data.Nat
open import Data.Bool
open import Data.List





{-"\underline{\textsc{Agda}_{\phantom{g}}
              \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad}"-}

data Ty : Set where  I : Ty
                     B : Ty 

data Val : Ty -> Set where
  IV  : ℕ    -> Val I
  BV  : Bool -> Val B

plusV : Val I -> Val I -> Val I
plusV (IV n) (IV m) = IV (n + m)

ifV : Val B -> {t : Ty} -> Val t -> Val t -> Val t
ifV (BV b) v1 v2 = if b then v1 else v2

{-""-}

data Expr : Ty -> Set where
  VAL   : {t : Ty} -> Val t -> Expr t
  PLUS  : Expr I -> Expr I -> Expr I
  IF    : Expr B ->
          {t : Ty} -> Expr t -> Expr t -> Expr t

eval : {t : Ty} -> Expr t -> Val t
eval (VAL v)        = v
eval (PLUS e1 e2)   =
  plusV  (eval e1) (eval e2)
eval (IF e0 e1 e2)  =
  ifV (eval e0) (eval e1) (eval e2)





{-"\underline{\textsc{Agda}_{\phantom{g}}^{\phantom{A^k}}
              \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\quad~~} "-}
{-""-}
data GList {Ix : Set} (X : Ix -> Ix -> Set) : Ix -> Ix -> Set
  where
    GNil   : {i : Ix} -> GList X i i
    GCons  : {i j k : Ix} ->
             X i j -> GList X j k -> GList X i k

{-""-}

append : {Ix : Set} -> {X : Ix -> Ix -> Set} -> {i j k : Ix}
  {-"~~"-} -> GList X i j -> GList X j k -> GList X i k
append GNil ys            = ys
append  (GCons x xs)  ys  =
        {-"~"-}GCons x (append xs ys) 






{-"\underline{\textsc{Agda}_{\phantom{g}}
              \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad}"-}

data Inst : List Ty -> List Ty -> Set where
  PUSH   : {t : Ty} {ts : List Ty} ->
           Val t -> Inst ts (t ∷ ts) 
  ADD    : {ts : List Ty } ->
           Inst (I ∷ I ∷ ts) (I ∷ ts)
  IFPOP  : {ts ts' : List Ty} ->
           GList Inst ts ts' ->
           GList Inst ts ts' ->
           Inst (B ∷ ts) ts'

Code : List Ty -> List Ty -> Set
Code sc sc' = GList Inst sc sc'

compile  : {t : Ty} -> {ts : List Ty} ->
           Expr t -> Code ts (t ∷ ts)
compile (VAL v)       =
  GCons (PUSH v) GNil
compile (PLUS e1 e2)  =
  append  (append  (compile e1) (compile e2)) 
          (GCons ADD GNil)
compile (IF e e1 e2)  =
  append  (compile e)
          (GCons  (IFPOP  (compile e1)
                          (compile e2))
                  GNil)





-- instantiating to a plain list 

record Unit : Set where constructor <>

List' : Set -> Set
List' a = GList (λ i j -> a) <> <>
 
nil' : {a : Set} -> List' a
nil' = GNil

cons' : {a : Set} -> a -> List' a -> List' a
cons' = GCons

-- instantiating to a length indexed list

Vec : Set -> ℕ -> Set
Vec a n = GList (λ i j -> a) n zero

vNil : {a : Set} -> Vec a zero
vNil = GNil

vCons  : {a : Set} {n : ℕ} ->
         a -> Vec a n -> Vec a (suc n)
vCons = GCons
