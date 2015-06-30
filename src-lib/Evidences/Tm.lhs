Tm
==

> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, ConstraintKinds,
>     GeneralizedNewtypeDeriving, PatternSynonyms, DataKinds, TupleSections,
>     CPP #-}

> module Evidences.Tm where

> import Prelude hiding (foldl)
> import Control.Applicative
> import Control.Monad.State
> import Control.Monad.Trans.Error
> import qualified Data.Monoid as M
> import Data.Monoid (mappend, mconcat, mempty, (<>))
> import Data.Foldable
> import Data.Functor.Identity
> import Data.List hiding (foldl)
> import Data.Traversable

> import Control.Error

> import Kit.MissingLibrary
> import Kit.BwdFwd
> import NameSupply.NameSupply

#ifdef __GHCJS__

This is annoying. GHCJS and GHC are using different versions of base or
something. Even though they're both listed as 4.8.0.0

> import Control.Monad

> instance Alternative (Either (StackError e)) where
>     empty = Left (errMsgStack "empty alternative")
>     (Left _) <|> x = x
>     x        <|> _ = x
>
> instance MonadPlus (Either (StackError e)) where
>     mzero = empty
>     mplus = (<|>)

#endif

Syntax of Terms and Values
--------------------------

We distinguish `In`Terms (into which we push types) and `Ex`Terms (from
which we pull types).

> data Dir = In | Ex

This is the by-now traditional bidirectional
type-checking @turner:bidirectional_tc story: there are *checkable*
terms that are checked against given types, and there are *inferable*
terms whose types are inferred relative to a typing context. We push
types in to checkable terms, and pull types from inferable terms.

And, of course, we're polymorphic in the representation of free
variables, like your mother always told you. This gives the following
signature for a term:

> data Tm :: Dir -> * -> * where

We can push types into:

* lambda terms;
* canonical terms; and
* inferred terms.

>   L     :: Scope x          -> Tm In x -- ^ lambda
>   C     :: Can (Tm In x)    -> Tm In x -- ^ canonical
>   N     :: Tm Ex x          -> Tm In x -- ^ `Ex` to `In`

And we can infer types from:

* parameters, because they carry their types;
* variables, by reading the context;
* fully applied operators, by `opTy` defined below;
* elimination, by the type of the eliminator; and
* type ascription on a checkable term, by the ascripted type.

>   P     :: x                         -> Tm Ex x -- ^ parameter
>   V     :: Int                       -> Tm Ex x -- ^ variable
>   (:@)  :: Op -> [Tm In x]           -> Tm Ex x -- ^ fully applied op
>   (:$)  :: Tm Ex x -> Elim (Tm In x) -> Tm Ex x -- ^ elim
>   (:?)  :: Tm In x -> Tm In x        -> Tm Ex x -- ^ typing
>   Yuk   :: Tm In x                   -> Tm Ex x -- ^ dirty

To put some flesh on these bones, we define and use the `Scope`, `Can`,
`Op`, and `Elim` data-types. Their role is described below. Before that,
let us point out an important invariant. Non-implementers are advised to
skip the following.

[Neutral terms and Operators]

In the world of values, i.e. `Tm In`, the neutral
terms are exactly the `N t` terms. Enforcing this invariant requires
some caution in the way we deal with operators and how we turn them into
values, so this statement relies on the hypothesis that the evaluation
of operators is correct: it is not enforced by Haskell type-system.

To prove that statement, we first show that any `Tm In` which is not a `N t`
is not a neutral term. This is obvious as we are left with lambda and
canonicals, which cannot be stuck. Then, we have to prove that a `N t` in `Tm
In p` form is a stuck term.  We do so by case analysis on the term `t` inside
the `N`:

-   Typing and variables will not let you get values, so a neutral value
    is not one of those.

-   This is also easy if you have a parameter: it is stuck waiting for
    its definition.

-   An eliminator in value form consists in an elimination applied to a
    value in `Ex`, which is – by induction – a neutral term. Hence, the
    eliminator is stuck too.

-   The case for fully applied operator is more problematic: we need one
    of the arguments to be a `N t`, and to be used by `Op`. This way,
    the operation is indeed a neutral term. We can hardly enforce this
    constraint in Haskell type system, so we have to deal with this
    approximation.

As a consequence, fully applied operators call for some care. If you are
to explicitly write a `:@` term wrapped inside a `N`, you must be sure
that the operator is indeed applied to a stuck term *which is used* by
the operator. During evaluation, for example, we have been careful in
returning a neutral operator if and only if the operator was consuming a
stuck term. As a corollary, if the operator can be fully computed, then
it *must* be so.

More tricky but for the same reason: when *implementing* term builders
(not when using them), we are indeed making terms, potentially involving
operators. Again, we must be careful of not building a stuck operator
for no good reason.

> (-$) :: VAL -> [INTM] -> INTM
> f -$ as = N (foldl (\g a -> g :$ A a) (Yuk f) as)

Scopes

TODO(joel) update outdated note
A `Scope` represents the body of a binder, but the representation
differs with phase. In *terms*, `x :. t` is a *binder*: the `t` is a de
Bruijn term with a new bound variable 0, and the old ones incremented.
The `x` is just advice for display name selection.

It is important to ensure that `body` computes to a fully evaluated
value, otherwise say "good bye" to strong normalisation.

In both cases, we represent constant functions with `K t`, equivalent of
`\_ -> t`.

> data Scope :: * -> * where
>   (:.)  :: String -> Tm In x           -> Scope x  -- binding
>   H     :: Env x -> String -> Tm In x  -> Scope x
>   K     :: Tm In x                     -> Scope x  -- constant

Canonical objects

The `Can` functor explains how canonical objects are constructed from
sub-objects (terms or values, as appropriate). Lambda is not included
here: morally, it belongs; practically, adapting `Can` to support
binding complicates the definition.

> data Can           :: * -> * where
>     Set            :: Can t                                   -- set of sets
>     Pi             :: t -> t -> Can t                         -- functions
>     Con            :: t -> Can t                              -- packing

Desc

>     Mu             :: Labelled Identity t -> Can t

IDesc

>     IMu            :: Labelled (Identity :*: Identity) t -> t -> Can t

Enum

>     EnumT          :: t -> Can t
>     Ze             :: Can t
>     Su             :: t -> Can t

Equality

>     EqBlue         :: (t :>: t) -> (t :>: t) -> Can t

Free Monad

>     Monad          :: t -> t -> Can t
>     Return         :: t -> Can t
>     Composite      :: t -> Can t

Labelled Types (chopping block)

>     Label          :: t -> t -> Can t
>     LRet           :: t -> Can t

Nu

Nu (ml : [Set?] :?=: Id (x : desc?)) : Set
Con (y : (descOp @@ [x, C t])) : t@(Nu (_ :?=: Id x))
CoIt (d : desc) (sty : Set) (f : sty -> descOp @@ [x, styv]) (s : sty)
    : Nu (_ :?=: Id x)

>     Nu             :: Labelled Identity t -> Can t
>     CoIt           :: t -> t -> t -> t -> Can t

Prob

>     Prob           :: Can t
>     ProbLabel      :: t -> t -> t -> Can t
>     PatPi          :: t -> t -> t -> Can t
>     Sch            :: Can t
>     SchTy          :: t -> Can t
>     SchExpPi       :: t -> t -> Can t
>     SchImpPi       :: t -> t -> Can t

Prop

Prop : Set
Prf (p : Prop) : Set
Trivial : Prop
Absurd : Prop
And : (p : Prop) (q : Prop) : Prop
All (s : Set) (p : s -> Prop) : Prop
(Box . Irr) (x : Prf p) : Prf p
Pair (x : Prf p) (y : Prf q) : Prf (And p q)
Void : Prf Trivial
Inh (ty : Set) : Prop
Wit (t : ty) : Prf (Inh ty)

>     Prop           :: Can t
>     Prf            :: t -> Can t
>     Trivial        :: Can t
>     Absurd         :: Can t
>     And            :: t -> t -> Can t
>     All            :: t -> t -> Can t
>     Box            :: Irr t -> Can t
>     Inh            :: t -> Can t
>     Wit            :: t -> Can t

Quotients

Quotient (x : Set) (r : xv -> xv -> Prop) (p : Prf (equivalenceRelation x r))
    : Set
Con (x : a) : Quotient a r p

>     Quotient       :: t -> t -> t -> Can t

Records

RSig : Set
REmpty : RSig
RCons (sig : RSig) (id : UId) (ty : ?? -> Set) : RSig
Record (ml : [Set?] :?=: Id (r : RSig)) : Set

>     RSig           :: Can t
>     REmpty         :: Can t
>     RCons          :: t -> t -> t -> Can t
>     Record         :: Labelled Identity t -> Can t

Sigma

Unit : Set
Void : Unit
Sigma (s : Set) (t : s -> Set) : Set
Pair (x : s) (y : (t x)) : Sigma s t

>     Unit           :: Can t
>     Void           :: Can t
>     Sigma          :: t -> t -> Can t
>     Pair           :: t -> t -> Can t

UId

>     UId            :: Can t
>     Tag            :: String -> Can t

Anchors

Anchors : Set
Anchor (u : UId) (t : Set) (ts : AllowedBy t) : Anchors
AllowedBy (t : Set) : Set
AllowedEpsilon : AllowedBy t
AllowedCons
    (S : Set)
    (T : S -> Set)
    (q : ty = Pi S T)
    (s : S)
    (ts : AllowedBy (T s))
    : AllowedBy ty

>     Anchors        :: Can t
>     Anchor         :: t -> t -> t -> Can t
>     AllowedBy      :: t -> Can t
>     AllowedEpsilon :: Can t
>     AllowedCons    :: t -> t -> t -> t -> t -> Can t

>   deriving (Show, Eq)

The `Con` object is used and abused in many circumstances. However, all
its usages share the same pattern: `Con` is used whenever we need to
"pack" an object `t` into something else, to avoid ambiguities. For
example, we use `Con` in the following case:

$$\Rule{desc x (Mu x) \ni y}
     {Mu x \ni Con y}$$

Eliminators

The `Elim` functor explains how eliminators are constructed from their
sub-objects. It's a sort of logarithm @hancock:amen. Projective
eliminators for types with $\eta$-laws go here.

> data Elim :: * -> * where
>   A     :: t -> Elim t                             -- application
>   Out   :: Elim t                                  -- unpacks Con
>   Call  :: t -> Elim t
>   Fst   :: Elim t
>   Snd   :: Elim t
>   deriving (Show, Eq)

Just as `Con` was packing things up, we define here `Out` to unpack
them.

Eliminators can be chained up in a *spine*. A `Spine` is a list of
eliminators for terms, typically representing a list of arguments that
can be applied to a term with the `$:$` operator.

> type Spine x = [Elim (Tm In x)]

> ($:$) :: Tm Ex x -> Spine x -> Tm Ex x
> ($:$) = foldl (:$)

Operators

Other computation is performed by a fixed repertoire of operators. To
construct an operator, you need a name (for scope resolution and
printing), an arity (so the resolver can manage fully applied usage), a
typing telescope, a computation strategy, and a simplification method.

> data Op = Op
>   { opName  :: String
>   , opArity :: Int
>   , opTyTel :: TEL TY
>   , opSimp  :: Alternative m => [VAL] -> NameSupply -> m NEU
>   , opRun   :: [VAL] -> Either NEU VAL
>   }

A key component of the definition of operators is the typing telescope.
Hence, we first describe the implementation of the telescope.

Telescope

A telescope `TEL` represents the standard notion of telescope in Type
Theory. This consists in a sequence of types which definition might rely
on any term inhabiting the previous types. A telescope is terminated by
a `Target`.

> data TEL x  = Target x
>             | (String :<: TY) :-: (VAL -> TEL x)
> infix 3 :-:

The interpretation of the telescope is carried by `telCheck`. On the
model of `opTy` defined below, this interpretation uses a generic
checker-evaluator `chev`. Based on this chev, it simply goes over the
telescope, checking and evaluating as it moves further.

> telCheck :: forall m t s x. (Monad m, ErrorStack m t)
>          => (TY :>: t -> m (s :=>: VAL))
>          -> (TEL x :>: [t])
>          -> m ([s :=>: VAL] , x)
> telCheck _ (Target x :>: []) = return ([] , x)
> telCheck chev ((_ :<: sS :-: tT) :>: (s : t)) = do
>     ssv@(_ :=>: sv) <- chev (sS :>: s)
>     (svs , x) <- telCheck chev (tT sv :>: t)
>     return (ssv : svs , x)
> telCheck _ _ = throwStack (errMsgStack "telCheck: opTy mismatch" :: StackError t)

Running the operator

The `opRun` field implements the computational behavior: given suitable
arguments, we should receive a value, or failing that, the neutral term
to blame for the failure of computation. For example, if `append` were
an operator, it would compute if the first list is nil or cons, but
complain about the first list if it is neutral.

Useful Abbreviations
--------------------

We have some pattern synonyms for common, er, patterns.

> pattern SET       = C Set                -- set of sets
> pattern ARR s t   = C (Pi s (L (K t)))   -- simple arrow
> pattern PI s t    = C (Pi s t)           -- dependent functions
> pattern CON t     = C (Con t)            -- Container (packing "stuff")
> pattern NV n      = N (V n)              -- Variable (bound)
> pattern NP n      = N (P n)              -- Parameter (free)
> pattern LAV x t   = L (x :. t)           -- Lambda (with variable)
> pattern LK t      = L (K t)              -- Lambda (with constant)
> pattern PIV x s t = PI s (LAV x t)       -- Pi (with variable)

Anchors

> pattern ANCHORS        = C Anchors
> pattern ANCHOR u t ts  = C (Anchor u t ts)
> pattern ALLOWEDBY t    = C (AllowedBy t)
> pattern ALLOWEDEPSILON = C AllowedEpsilon
> pattern ALLOWEDCONS _S _T q s ts = C (AllowedCons _S _T q s ts)

Equality

> pattern EQBLUE p q = C (EqBlue p q)

Sigma

> pattern SIGMA p q = C (Sigma p q)
> pattern PAIR  p q = C (Pair p q)
> pattern UNIT      = C Unit
> pattern VOID      = C Void
> pattern Times x y = Sigma x (L (K y))
> pattern TIMES x y = C (Times x y)

UId

> pattern UID    = C UId
> pattern TAG s  = C (Tag s)

Enum

> pattern ZE         = C Ze
> pattern SU n       = C (Su n)
> pattern NILN       = ZE
> pattern CONSN      = SU ZE
> pattern ENUMT e    = C (EnumT e)
> pattern NILE       = CON (PAIR NILN VOID)
> pattern CONSE t e  = CON (PAIR CONSN (PAIR t (PAIR e VOID)))

Desc

> pattern MU l x        = C (Mu (l :?=: Identity x))

Define a bunch of codes for the primitives of this universe:

> pattern IDN     = ZE
> pattern CONSTN  = SU ZE
> pattern SUMN    = SU (SU ZE)
> pattern PRODN   = SU (SU (SU ZE))
> pattern SIGMAN  = SU (SU (SU (SU ZE)))
> pattern PIN     = SU (SU (SU (SU (SU ZE))))

... And their representation.

> pattern IDD           = CON (PAIR IDN     VOID)
> pattern CONSTD x      = CON (PAIR CONSTN  (PAIR x VOID))
> pattern SUMD e b      = CON (PAIR SUMN    (PAIR e (PAIR b VOID)))
> pattern PRODD u d d'  = CON (PAIR PRODN   (PAIR u (PAIR d (PAIR d' VOID))))
> pattern SIGMAD s t    = CON (PAIR SIGMAN  (PAIR s (PAIR t VOID)))
> pattern PID s t       = CON (PAIR PIN     (PAIR s (PAIR t VOID)))

IDesc

> pattern IMU l ii x i  = C (IMu (l :?=: (Identity ii :& Identity x)) i)

Define a bunch of codes for the primitives of this universe:

> pattern IVARN     = ZE
> pattern ICONSTN   = SU ZE
> pattern IPIN      = SU (SU ZE)
> pattern IFPIN     = SU (SU (SU ZE))
> pattern ISIGMAN   = SU (SU (SU (SU ZE)))
> pattern IFSIGMAN  = SU (SU (SU (SU (SU ZE))))
> pattern IPRODN    = SU (SU (SU (SU (SU (SU ZE)))))

... And their representation

> pattern IVAR i        = CON (PAIR IVARN     (PAIR i VOID))
> pattern IPI s t       = CON (PAIR IPIN      (PAIR s (PAIR t VOID)))
> pattern IFPI s t      = CON (PAIR IFPIN     (PAIR s (PAIR t VOID)))
> pattern ISIGMA s t    = CON (PAIR ISIGMAN   (PAIR s (PAIR t VOID)))
> pattern IFSIGMA s t   = CON (PAIR IFSIGMAN  (PAIR s (PAIR t VOID)))
> pattern ICONST p      = CON (PAIR ICONSTN   (PAIR p VOID))
> pattern IPROD u x y   = CON (PAIR IPRODN    (PAIR u (PAIR x (PAIR y VOID))))

FreeMonad

> pattern MONAD d x   = C (Monad d x)
> pattern RETURN x    = C (Return x)
> pattern COMPOSITE t = C (Composite t)

Labelled Types (chopping block)

> pattern LABEL l t = C (Label l t)
> pattern LRET t    = C (LRet t)

Nu

> pattern NU l t = C (Nu (l :?=: Identity t))
> pattern COIT d sty f s = C (CoIt d sty f s)

Prob

> pattern PROB             = C Prob
> pattern PROBLABEL u s a  = C (ProbLabel u s a)
> pattern PATPI u s p      = C (PatPi u s p)
> pattern SCH              = C Sch
> pattern SCHTY s          = C (SchTy s)
> pattern SCHEXPPI s t     = C (SchExpPi s t)
> pattern SCHIMPPI s t     = C (SchImpPi s t)

Prop

> pattern PROP        = C Prop
> pattern PRF p       = C (Prf p)
> pattern ALL p q     = C (All p q)
> pattern IMP p q     = ALL (PRF p) (L (K q))
> pattern ALLV x s p  = ALL s (LAV x p)
> pattern AND p q     = C (And p q)
> pattern TRIVIAL     = C Trivial
> pattern ABSURD      = C Absurd
> pattern BOX p       = C (Box p)
> pattern INH ty      = C (Inh ty)
> pattern WIT t       = C (Wit t)

Quotients

> pattern QUOTIENT x r p = C (Quotient x r p)
> pattern CLASS x        = C (Con x)

Records

> pattern RSIG         = C RSig
> pattern REMPTY       = C REmpty
> pattern RCONS s i t  = C (RCons s i t)
> pattern RECORD l s   = C (Record (l :?=: Identity s))

We have some type synonyms for commonly occurring instances of `Tm`.

> type InTm   = Tm In
> type INTM   = InTm REF
> type VAL    = InTm REF
> type TY     = VAL

> type ExTm   = Tm Ex
> type EXTM   = ExTm REF
> type NEU    = ExTm REF

> type Env x  = (Bwd (Tm In x), TXTSUB)  -- values for deBruijn indices
> type ENV    = Env REF
> type TXTSUB = [(Char, String)]        -- renaming plan

We have special pairs for types going into and coming out of stuff. We
write `typ :>: thing` to say that `typ` accepts the term `thing`,
i.e. we can push the `typ` in the `thing`. Conversely, we write `thing
:<: typ` to say that `thing` is of inferred type `typ`, i.e. we can pull
the type `typ` out of the `thing`. Therefore, we can read `:>:` as
"accepts" and `:<:` as "has inferred type".

> data ty :>: tm = ty :>: tm  deriving (Show, Eq)
> infix 4 :>:

> data tm :<: ty = tm :<: ty  deriving (Show, Eq)
> infix 4 :<:

> fstIn :: (a :>: b) -> a
> fstIn (x :>: _) = x

> sndIn :: (a :>: b) -> b
> sndIn (_ :>: x) = x

> fstEx :: (a :<: b) -> a
> fstEx (x :<: _) = x

> sndEx :: (a :<: b) -> b
> sndEx (_ :<: x) = x

As we are discussing syntactic sugar, we define the "reduces to" symbol:

> data t :=>: v = t :=>: v deriving (Show, Eq)
> infix 5 :=>:

with the associated projections:

> valueOf :: (t :=>: v) -> v
> valueOf (_ :=>: v) = v

> termOf :: (t :=>: v) -> t
> termOf (t :=>: _) = t

Intuitively, `t :=>: v` can be read as "the term `t` reduces to the
value `v`".

We use `(??)` as a smart constructor for type ascriptions that omits
them when the term is in fact neutral.

> (??) :: INTM -> INTM -> EXTM
> (N t) ?? _   = t
> t     ?? ty  = t :? ty

<a name="Evidences.Tm.syntactic-equality">Syntactic Equality</a>
------------------

In the following, we implement definitional equality on terms. In this
case, it's mainly structural.

> instance Eq x => Eq (Tm d x) where

First, a bunch of straightforward structural inductions:

>   L s0          == L s1          = s0 == s1
>   C c0          == C c1          = c0 == c1
>   N n0          == N n1          = n0 == n1
>   P x0          == P x1          = x0 == x1
>   V i0          == V i1          = i0 == i1
>   (t0 :$ e0)    == (t1 :$ e1)    = t0 == t1 && e0 == e1
>   (op0 :@ vs0)  == (op1 :@ vs1)  = op0 == op1 && vs0 == vs1

Then, equality of a type ascription means having equal elements:

>   (t0 :? _)     == (t1 :? _)     = t0 == t1

Otherwise, they are clearly not equal:

>   _             == _             = False

We compare scopes ignoring name advice: de Bruijn indexing gets rid of
$\alpha$-conversion issues. When checking the definitional equality, we
should only ever see full binders thanks to $\eta$-expansion; the
remaining cases are for sound but not complete approximation of the
definitional equality.

> instance Eq x => Eq (Scope x) where
>   (_ :. t0)  == (_ :. t1)  = t0 == t1
>   K t0       == K t1       = t0 == t1
>   _          == _          = False

Operators are compared by name!

> instance Eq Op where
>   op0 == op1 = opName op0 == opName op1

We provide a smashing operator, for things whose precise values are
irrelevant. We intend this for proofs, but there may be other things
(like name advice) for which we should use it.

> data Irr x = Irr x deriving Show
> instance Eq (Irr x) where
>   _ == _ = True

In this section, we have defined the syntactic equality on terms. The general
definition of syntactic equality remains to be done. It is the subject of
Section [Evidences.DefinitionalEquality](#Evidences.DefinitionalEquality):
there, we rely on *quotation* to turn values into terms. Once turned into
terms, we fall back to the equality defined above.

<a name="Evidences.Tm.references">References</a>
----------

References are the key way we represent free variables, declared,
defined, and deluded. References carry not only names, but types and
values, and are shared.

> data REF = (:=) { refName :: Name, refBody :: (RKind :<: TY)}
> infix 2 :=

References are compared by name, as the `NameSupply` guarantees a source
of unique, fresh names. Note however that `REF`s being shared, one could
think of using physical pointer equality to implement this test (!).
This would require us to ensure we retain sharing in all circumstances,
however.

> instance Eq REF where
>   (x := _) == (y := _) = x == y

> instance Show REF where
>   show (name := kt) = unwords
>       [ "\"" ++ intercalate "." (map (\(x,n) -> x ++ "_" ++ show n) name) ++ "\""
>       -- , ":="
>       -- , show kt ++ ")"
>       ]

A `REF` can be of one of four kinds:

-   `DECL`: used a binder, a declaration;

-   `DEFN`: computed, a definition;

-   `HOLE`: not computed yet, a definition-to-be; or

-   `FAKE`: a hysterectomized definition, used to make labels.

> data RKind
>   =  DECL
>   |  DEFN VAL
>   |  HOLE HKind
>   |  FAKE
>   deriving Show

A hole will be in one of three "Buddy Holly" states:

-   `Crying`: the elaboration strategy intended to solve the hole has
    gone wrong.

-   `Waiting`: a solution strategy exists for the hole (including the
    "strategy" of waiting for the user to solve it).

-   `Hoping`: no solution strategy is assigned to the hole, so it will
    take any value that you can give it.

Stealing documentation from http://www.e-pig.org/epilogue/?p=147 might
be a good idea at this point.

> data HKind = Crying String | Waiting | Hoping
>   deriving Show

We can already define some handy operators on `REF`s. First, we can turn
a `REF` to a `VAL`ue by using `pval`. If the reference is already
defined, then we pick the computed value. Otherwise, it is dealt with as
a neutral parameter.

> pval :: REF -> VAL
> pval (_ := DEFN v :<: _)  = v
> pval r                    = NP r

Second, we can extract the type of a reference thanks to the following
code:

> pty :: REF -> VAL
> pty (_ := _ :<: ty) = ty

Labels
------

Labels are tucked into strange places, in order to record the high-level
presentation of low-level stuff. A typical label is the neutral
application of a fake reference — a definition whose hysterectomy stops
it computing.

> data Labelled f t
>   = Maybe t :?=: f t
>   deriving (Show)

For example, labels are used in the presentation of the `Enum`
(Section [Features.Enum]) and `Desc` (Section [sec:Features.Desc](#Features.Enum]) and `Desc` (Section [sec:Features.Desc))
data-types. These data-types are themselves implemented as fix-points of
non human-readable descriptions, hence we hide the details behind a
label. The curious reader is referred to their implementation. Anybody
in their right mind would ignore labels for now.

Label equality is sound but not complete for equality of what has been
labelled.

> instance (Traversable f, HalfZip f, Eq t) => Eq (Labelled f t) where
>   (Just a  :?=: _)  ==  (Just b  :?=: _) | a == b  = True
>   (_       :?=: s)  ==  (_       :?=: t)           = case halfZip s t of
>     Nothing -> False
>     Just x -> M.getAll (crush (M.All . uncurry (==)) x)

If we have a labelled `INTM`, we can try to extract the name from the
label.

> extractREF :: EXTM -> Maybe REF
> extractREF (P ref)    = Just ref
> extractREF (tm :$ _)  = extractREF tm
> extractREF _          = Nothing

We can compare value labels in a sound but incomplete fashion:

> eqLabelIncomplete :: Eq t => Labelled f t -> Labelled f t -> Bool
> eqLabelIncomplete (Just x :?=: _)  (Just y :?=: _)  = x == y
> eqLabelIncomplete _                _                = False

We can also throw away a label, should we want to.

> dropLabel :: Labelled f t -> Labelled f t
> dropLabel (_ :?=: a) = (Nothing :?=: a)

Term Construction
-----------------

It is sometimes useful to construct the identity function:

> idVAL :: String -> Tm In x
> idVAL x   = L (x :. (N (V 0)))

> idTM :: String -> INTM
> idTM = idVAL

> ($#) :: Int -> [Int] -> InTm x
> f $# xs = N (foldl (\ g x -> g :$ A (NV x)) (V f) xs)

The aptly named `$##` operator applies an `ExTm` to a list of `InTm`s.

> ($##) :: (Functor t, Foldable t) => ExTm x -> t (InTm x) -> ExTm x
> f $## xs = foldl (\ v w -> v :$ A w) f xs

Sensible name advice is a hard problem. The `fortran` function tries to
extract a useful name from a binder.

> fortran :: Tm In x -> String
> fortran (L (x :. _))  | not (null x) = x
> fortran (L (H _ x _)) | not (null x) = x
> -- XXX(joel) this is unacceptable. Actually, on second thought we should
> -- never get here... This message is unlikely to be helpful, but worth a try.
> fortran xt = "(XXX(joel) fortran unexpectedly called)"

Similarly, it is useful to extract name advice from a `REF`.

> refNameAdvice :: REF -> String
> refNameAdvice = fst . last . refName

If we have a bunch of references we can make them into a spine:

> toSpine :: Foldable f => f REF -> Spine REF
> toSpine = foldMap (\ r -> [A (NP r)])

Error Stack
-----------

This is a first try, with some shortcomings. Feel free to modify the
following to make it suit your need.

> data ErrorTok t
>     = StrMsg        String
>     | ErrorTm       (t       :<: Maybe t)
>     | ErrorCan      (Can t)
>     | ErrorElim     (Elim t)
>     | ErrorREF      REF
>     | ErrorVAL      (VAL     :<: Maybe TY)

> instance Show t => Show (ErrorTok t) where
>     show (StrMsg str) = str
>     show (ErrorTm (tm :<: ty)) = tmValShow "term" tm ty
>     show (ErrorCan c) = "(can) [" <> show c <> "]"
>     show (ErrorElim e) = "(elim) [" <> show e <> "]"
>     show (ErrorREF r) = "(ref) [" <> show r <> "]"
>     show (ErrorVAL (tm :<: ty)) = tmValShow "val" tm ty

> tmValShow :: Show t => String -> t -> Maybe t -> String
> tmValShow prefix tm ty = mconcat
>         [ "(" <> prefix <> ") ["
>         , show tm
>         , case ty of
>               Just ty' -> " : " <> show ty'
>               Nothing  -> ""
>         , "]"
>         ]

> instance Functor ErrorTok where
>     fmap _ (StrMsg x)            = StrMsg x
>     fmap f (ErrorTm (t :<: mt))  = ErrorTm (f t :<: fmap f mt)
>     fmap f (ErrorCan t)          = ErrorCan (fmap f t)
>     fmap f (ErrorElim t)         = ErrorElim (fmap f t)
>     fmap _ (ErrorREF r)          = ErrorREF r
>     fmap _ (ErrorVAL (t :<: mt)) = ErrorVAL (t :<: mt)

An error is list of error tokens:

> type ErrorItem t = [ErrorTok t]

> showErrorItem :: Show t => ErrorItem t -> String
> showErrorItem = unlines . map show

Errors a reported in a stack, as failure is likely to be followed by
further failures. The top of the stack is the head of the list.

> newtype StackError t = StackError { unStackError :: [ErrorItem t] }

> prePostStr :: String -> String -> String -> String
> prePostStr pre post str = pre <> str <> post

> instance Show t => Show (StackError t) where
>     show = prePostStr "StackError (\n" "\n)"
>          . unlines
>          . map showErrorItem
>          . unStackError

> -- XXX(joel) this is gross
> -- With ProofStateT, we use the alternative instance for StateT, which
> -- requires MonadPlus Either, which requires Error (StackError e).
> instance Error (StackError e) where
>     noMsg = errMsgStack "something went wrong"
>     strMsg = errMsgStack

> class ErrorStack m e where
>     throwStack :: StackError e -> m a
>     catchStack :: m a -> (StackError e -> m a) -> m a

> instance ErrorStack (Either (StackError e)) e where
>     throwStack = Left
>     catchStack = catchE

> instance (Monad m, ErrorStack m e) => ErrorStack (StateT s m) e where
>     throwStack = lift . throwStack
>     catchStack m h = StateT $ \st ->
>         (runStateT m st) `catchStack` (\e -> runStateT (h e) st)

> instance M.Monoid (StackError t) where
>   (StackError a) `mappend` (StackError b) = StackError (a ++ b)
>   mempty = StackError []

To ease the writing of error terms, we have a bunch of combinators:

> stackItem :: [ErrorItem t] -> StackError t
> stackItem = StackError . pure . mconcat

> errMsg :: String -> ErrorItem t
> errMsg s = [StrMsg s]

> errMsgStack :: String -> StackError t
> errMsgStack = StackError . pure . errMsg

> errTm :: t -> ErrorItem t
> errTm t = [ErrorTm (t :<: Nothing)]

> errCan :: Can t -> ErrorItem t
> errCan t = [ErrorCan t]

> errTyVal :: (VAL :<: VAL) -> ErrorItem t
> errTyVal (t :<: ty) = [ErrorVAL (t :<: Just ty)]

> errVal :: VAL -> ErrorItem t
> errVal t = [ErrorVAL (t :<: Nothing)]

> errElim :: Elim t -> ErrorItem t
> errElim t = [ErrorElim t]

> errRef :: REF -> ErrorItem t
> errRef r = [ErrorREF r]

> pushError :: (Monad m, ErrorStack m t)
>           => m a
>           -> StackError t
>           -> m a
> pushError c e = c `catchStack` (\x -> throwStack (e <> x))

> throwErrorS :: ErrorStack m t => [ErrorItem t] -> m a
> throwErrorS = throwStack . StackError

> catchMaybe :: (ErrorStack m t, Monad m)
>            => Maybe a
>            -> StackError t
>            -> m a
> catchMaybe (Just x) _ = return x
> catchMaybe Nothing  e = throwStack e

> catchEither :: (Monad m, ErrorStack m t)
>             => Either (StackError t) a
>             -> StackError t
>             -> m a
> catchEither (Right x) _ = return x
> catchEither (Left s) e = throwStack (e <> s)

> throwErrMsg :: ErrorStack m VAL => String -> m a
> throwErrMsg str =
>     let stack :: StackError VAL
>         stack = errMsgStack str
>     in throwStack stack

throwErrTm :: Monad m => t -> StackErrorT t m a
throwErrTm = throwStack . StackError . pure . errTm

> convertErrorVALs :: ErrorTok VAL -> ErrorTok t
> convertErrorVALs (StrMsg s)             = StrMsg s
> convertErrorVALs (ErrorTm tt)           = ErrorVAL tt
> convertErrorVALs (ErrorCan c)           = ErrorVAL (C c :<: Nothing)
> convertErrorVALs (ErrorElim e)          = StrMsg $ "ErrorElim " ++ show e
> convertErrorVALs (ErrorREF r)           = ErrorREF r
> convertErrorVALs (ErrorVAL tt)          = ErrorVAL tt

> instance Traversable Can where
>     traverse _ Set       = pure Set
>     traverse f (Pi s t)  = Pi <$> f s <*> f t
>     traverse f (Con t)   = Con <$> f t
>     traverse _ Anchors = pure Anchors
>     traverse f (Anchor u t ts) = Anchor <$> f u <*> f t <*> f ts
>     traverse f (AllowedBy t) = AllowedBy <$> f t
>     traverse f AllowedEpsilon = pure AllowedEpsilon
>     traverse f (AllowedCons _S _T q s ts) =
>         AllowedCons <$> f _S <*> f _T <*> f q <*> f s <*> f ts
>     traverse f (Mu l) = Mu <$> traverse f l
>     traverse f (EnumT e)    = EnumT <$> f e
>     traverse _ Ze           = pure Ze
>     traverse f (Su n)       = Su <$> f n
>     traverse f (EqBlue (pty :>: p) (qty :>: q)) =
>       let trav1 = (:>:) <$> f pty <*> f p
>           trav2 = (:>:) <$> f qty <*> f q
>       in EqBlue <$> trav1 <*> trav2
>     traverse f (Monad d x)   = Monad <$> f d <*> f x
>     traverse f (Return x)    = Return <$> f x
>     traverse f (Composite x) = Composite <$> f x
>     traverse f (IMu l i)     = IMu <$> traverse f l <*> f i
>     traverse f (Label l t) = Label <$> f l <*> f t
>     traverse f (LRet t)    = LRet <$> f t
>     traverse f (Nu t) = Nu <$> traverse f t
>     traverse f (Record t) = Record <$> traverse f t
>     traverse f (CoIt d sty g s) = CoIt <$> f d <*> f sty <*> f g <*> f s
>     traverse _ Prob = pure Prob
>     traverse f (ProbLabel u s a) = ProbLabel <$> f u <*> f s <*> f a
>     traverse f (PatPi u s p) = PatPi <$> f u <*> f s <*> f p
>     traverse _ Sch = pure Sch
>     traverse f (SchTy t)      = SchTy <$> f t
>     traverse f (SchExpPi s t) = SchExpPi <$> f s <*> f t
>     traverse f (SchImpPi s t) = SchImpPi <$> f s <*> f t
>     traverse _ Prop      = pure Prop
>     traverse f (Prf p)   = Prf <$> f p
>     traverse f (All p q) = All <$> f p <*> f q
>     traverse f (And p q) = And <$> f p <*> f q
>     traverse _ Trivial   = pure Trivial
>     traverse _ Absurd    = pure Absurd
>     traverse f (Box p)   = Box <$> traverse f p
>     traverse f (Inh ty)  = Inh <$> f ty
>     traverse f (Wit t)   = Wit <$> f t
>     traverse f (Quotient x r p) = Quotient <$> f x <*> f r <*> f p
>     traverse _ RSig           = pure RSig
>     traverse _ REmpty         = pure REmpty
>     traverse f (RCons s i t)  = RCons <$> f s <*> f i <*> f t
>     traverse _ Unit         = pure Unit
>     traverse _ Void         = pure Void
>     traverse f (Sigma s t)  = Sigma <$> f s <*> f t
>     traverse f (Pair x y)   = Pair <$> f x <*> f y
>     traverse _ UId          = pure UId
>     traverse _ (Tag s)      = pure (Tag s)

> instance Functor Can where
>     fmap = fmapDefault

> instance Foldable Can where
>     foldMap = foldMapDefault

> instance HalfZip Can where
>     halfZip Set Set =
>         Just Set
>     halfZip (Pi s1 t1) (Pi s2 t2) =
>         Just $ Pi (s1,s2) (t1,t2)
>     halfZip (Con t1) (Con t2) =
>         Just $ Con (t1,t2)
>     halfZip Anchors Anchors =
>         Just Anchors
>     halfZip (Anchor u1 t1 ts1) (Anchor u2 t2 ts2) =
>         Just $ Anchor (u1, u2) (t1, t2) (ts1, ts2)
>     halfZip (AllowedBy t1) (AllowedBy t2) =
>         Just $ AllowedBy (t1, t2)
>     halfZip AllowedEpsilon AllowedEpsilon =
>         Just $ AllowedEpsilon
>     halfZip (AllowedCons _S1 _T1 q1 s1 ts1) (AllowedCons _S2 _T2 q2 s2 ts2) =
>         Just $ AllowedCons (_S1, _S2) (_T1, _T2) (q1, q2) (s1, s2) (ts1, ts2)
>     halfZip (Mu t0) (Mu t1) =
>         Mu <$> halfZip t0 t1
>     halfZip (EnumT t0) (EnumT t1) =
>         Just (EnumT (t0,t1))
>     halfZip Ze Ze =
>         Just Ze
>     halfZip (Su t0) (Su t1) =
>         Just (Su (t0,t1))
>     halfZip (Monad d1 x1) (Monad d2 x2) =
>         Just (Monad (d1, d2) (x1, x2))
>     halfZip (Return x) (Return y) =
>         Just (Return (x, y))
>     halfZip (Composite x) (Composite y) =
>         Just (Composite (x, y))
>     halfZip (IMu l0 i0) (IMu l1 i1) =
>         IMu <$> halfZip l0 l1 <*> pure (i0,i1)
>     halfZip (Label l1 t1) (Label l2 t2) =
>         Just (Label (l1,l2) (t1,t2))
>     halfZip (LRet x) (LRet y)           =
>         Just (LRet (x,y))
>     halfZip (Nu t0) (Nu t1)  =
>         Nu <$> halfZip t0 t1
>     halfZip (CoIt d0 sty0 g0 s0) (CoIt d1 sty1 g1 s1) =
>         Just (CoIt (d0,d1) (sty0,sty1) (g0,g1) (s0,s1))
>     halfZip Prob Prob =
>         Just Prob
>     halfZip (ProbLabel u1 s1 a1) (ProbLabel u2 s2 a2) =
>         Just $ ProbLabel (u1, u2) (s1, s2) (a1, a2)
>     halfZip (PatPi u1 s1 p1) (PatPi u2 s2 p2) =
>         Just $ PatPi (u1, u2) (s1, s2) (p1, p2)
>     halfZip Sch Sch =
>         Just Sch
>     halfZip (SchTy s1) (SchTy s2) =
>         Just $ SchTy (s1, s2)
>     halfZip (SchExpPi s1 t1) (SchExpPi s2 t2) =
>         Just $ SchExpPi (s1, s2) (t1, t2)
>     halfZip (SchImpPi s1 t1) (SchImpPi s2 t2) =
>         Just $ SchImpPi (s1, s2) (t1, t2)
>     halfZip Prop Prop =
>         Just Prop
>     halfZip (Prf p0) (Prf p1) =
>         Just (Prf (p0, p1))
>     halfZip (Quotient x r p) (Quotient y s q) =
>         Just (Quotient (x, y) (r, s) (p, q))
>     halfZip RSig RSig =
>         Just RSig
>     halfZip REmpty REmpty =
>         Just REmpty
>     halfZip (RCons s0 i0 t0)  (RCons s1 i1 t1)  =
>         Just (RCons (s0,s1) (i0,i1) (t0,t1))
>     halfZip Unit Unit =
>         Just Unit
>     halfZip (Sigma s0 t0) (Sigma s1 t1) =
>         Just (Sigma (s0,s1) (t0,t1))
>     halfZip Void Void =
>         Just Void
>     halfZip (Pair s0 t0) (Pair s1 t1) =
>         Just (Pair (s0,s1) (t0,t1))
>     halfZip UId UId =
>         Just UId
>     halfZip (Tag s) (Tag s')
>         | s == s' =
>         Just (Tag s)
>     halfZip _ _ =
>         Nothing

> instance Traversable Elim where
>   traverse f (A s)  = A <$> f s
>   traverse _ Out    = pure Out
>   traverse f (Call l) = Call <$> f l
>   traverse _ Fst  = pure Fst
>   traverse _ Snd  = pure Snd

> instance Functor Elim where
>     fmap = fmapDefault

> instance Foldable Elim where
>     foldMap = foldMapDefault

> instance HalfZip Elim where
>   halfZip (A s) (A t)  = Just $ A (s, t)
>   halfZip (Call t1) (Call t2) = Just (Call (t1, t2))
>   halfZip Fst Fst = pure Fst
>   halfZip Snd Snd = pure Snd
>   halfZip _ _          = Nothing

> instance Traversable Irr where
>   traverse f (Irr x) = Irr <$> f x

> instance Functor Irr where
>     fmap = fmapDefault

> instance Foldable Irr where
>     foldMap = foldMapDefault

> instance Show x => Show (Tm dir x) where
>   show (L s)       = "(L " ++ show s ++ ")"
>   show (C c)       = "(C " ++ show c ++ ")"
>   show (N n)       = "(N " ++ show n ++ ")"
>   show (P x)       = "(P \"" ++ show x ++ "\")"
>   show (V i)       = "V " ++ show i
>   show (n :$ e)    = "(" ++ show n ++ " :$ " ++ show e ++ ")"
>   show (op :@ vs)  = "(" ++ opName op ++ " :@ " ++ show vs ++ ")"
>   show (t :? y)    = "(" ++ show t ++ " :? " ++ show y ++ ")"
>   show (Yuk v)     = "((" ++ show v ++ "))"

> instance Show x => Show (Scope x) where
>   show (x :. t)   = show x ++ " :. " ++ show t
>   show (H g x t) = "(H " ++ show g ++ ") " ++ x ++ "(" ++ show t ++ ")"
>   show (K t) = "(K " ++ show t ++")"

> instance Show Op where
>   show = opName

> instance Traversable Scope where
>   traverse f (x :. t)   = (x :.) <$> traverse f t
>   traverse f (K t)      = K <$> traverse f t
>   traverse f (H (e, s) x t)  =
>     let foo = (,s) <$> traverse (traverse f) e
>     in H <$> foo <*> pure x <*> traverse f t

> instance Functor Scope where
>     fmap = fmapDefault

> instance Foldable Scope where
>     foldMap = foldMapDefault

> instance Traversable f => Traversable (Labelled f) where
>   traverse f (mt :?=: ft)  = (:?=:) <$> traverse f mt <*> traverse f ft

> instance Traversable f => Functor (Labelled f) where
>     fmap = fmapDefault

> instance Traversable f => Foldable (Labelled f) where
>     foldMap = foldMapDefault

> instance (Traversable f, HalfZip f) => HalfZip (Labelled f) where
>   halfZip (Just a  :?=: fs)  (Just b :?=: ft)  =
>     (Just (a, b)  :?=:) <$> halfZip fs ft
>   halfZip (_       :?=: fs)  (_      :?=: ft)  =
>     (Nothing  :?=:) <$> halfZip fs ft

> instance Traversable (Tm d) where
>   traverse f (L sc)     = L <$> traverse f sc
>   traverse f (C c)      = C <$> traverse (traverse f) c
>   traverse f (N n)      = N <$> traverse f n
>   traverse f (P x)      = P <$> f x
>   traverse _ (V i)      = pure (V i)
>   traverse f (t :$ u)   = (:$) <$> traverse f t <*> traverse (traverse f) u
>   traverse f (op :@ ts) = (op :@) <$> traverse (traverse f) ts
>   traverse f (tm :? ty) = (:?) <$> traverse f tm <*> traverse f ty
>   traverse f (Yuk tm)   = Yuk <$> traverse f tm

> instance Functor (Tm d) where
>     fmap = fmapDefault

> instance Foldable (Tm d) where
>     foldMap = foldMapDefault
