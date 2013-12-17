module Core (Ter(..), Def, Ident,Binder) where

import Control.Monad.Reader hiding (ap)
import Data.Graph
import Data.List (elemIndex)
import qualified MTT as A

type Binder = String

-- The core language:
data Ter = Var Binder
         | Id Ter Ter Ter | Refl Ter
         | Pi Ter Ter | Lam Binder Ter | App Ter Ter
         | Where Ter Def
         | U

         | Undef A.Prim

           -- constructor c Ms
         | Con Ident [Ter]

           -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Branch A.Prim [(Ident, ([Binder],Ter))]

           -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | LSum A.Prim [(Ident, [(Binder,Ter)])]

           -- TODO: Remove
         | TransInv Ter Ter Ter

           -- Trans type eqprof proof
           -- (Trans to be removed in favor of J ?)
           -- TODO: witness for singleton contractible and equation
         | Trans Ter Ter Ter

           -- (A B:U) -> Id U A B -> A -> B
           -- For TransU we only need the eqproof and the element in A is needed
         | TransU Ter Ter

           -- (A:U) -> (a : A) -> Id A a (transport A (refl U A) a)
           -- Argument is a
         | TransURef Ter

           -- The primitive J will have type:
           -- J : (A : U) (u : A) (C : (v : A) -> Id A u v -> U)
           --  (w : C u (refl A u)) (v : A) (p : Id A u v) -> C v p
         | J Ter Ter Ter Ter Ter Ter

           -- (A : U) (u : A) (C : (v:A) -> Id A u v -> U)
           -- (w : C u (refl A u)) ->
           -- Id (C u (refl A u)) w (J A u C w u (refl A u))
         | JEq Ter Ter Ter Ter

           -- Ext B f g p : Id (Pi A B) f g,
           -- (p : (Pi x:A) Id (Bx) (fx,gx)); A not needed ??
         | Ext Ter Ter Ter Ter

           -- Inh A is an h-prop stating that A is inhabited.
           -- Here we take h-prop A as (Pi x y : A) Id A x y.
         | Inh Ter

           -- Inc a : Inh A for a:A (A not needed ??)
         | Inc Ter

           -- Squash a b : Id (Inh A) a b
         | Squash Ter Ter

           -- InhRec B p phi a : B,
           -- p:hprop(B), phi:A->B, a:Inh A (cf. HoTT-book p.113)
           -- TODO?: equation: InhRec p phi (Inc a) = phi a
           --                  InhRec p phi (Squash a b) =
           --                     p (InhRec p phi a) (InhRec p phi b)
         | InhRec Ter Ter Ter Ter

           -- EquivEq A B f s t where
           -- A, B are types, f : A -> B,
           -- s : (y:B) -> fiber f y, and
           -- t : (y:B) (z : fiber f y) -> Id (fiber f y) (s y) z
           -- where fiber f y is Sigma x : A. Id B (f x) z.
         | EquivEq Ter Ter Ter Ter Ter

           -- (A : U) -> (s : (y : A) -> pathTo A a) ->
           -- (t : (y : B) -> (v : pathTo A a) -> Id (path To A a) (s y) v) ->
           -- Id (Id U A A) (refl U A) (equivEq A A (id A) s t)
         | EquivEqRef Ter Ter Ter

           -- (A B : U) -> (f : A -> B) (s : (y : B) -> fiber A B f y) ->
           -- (t : (y : B) -> (v : fiber A B f y) -> Id (fiber A B f y) (s y) v) ->
           -- (a : A) -> Id B (f a) (transport A B (equivEq A B f s t) a)
         | TransUEquivEq Ter Ter Ter Ter Ter Ter
  deriving (Show,Eq)

type Def = [(Binder,Ter)]       -- without type annotations for now
type Ident = String
