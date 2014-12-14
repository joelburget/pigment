Tm
==

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, RankNTypes,
>     MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
>     FlexibleContexts, ScopedTypeVariables, ConstraintKinds,
>     GeneralizedNewtypeDeriving, PatternSynonyms #-}
> module Evidences.Tm where
> import Prelude hiding (foldl)
> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.Except
> import qualified Data.Monoid as M
> import Data.Monoid (mempty, mappend, (<>))
> import Data.Foldable
> import Data.List hiding (foldl)
> import Data.Traversable
> import Kit.MissingLibrary
> import Kit.BwdFwd
> import NameSupply.NameSupply

Syntax of Terms and Values
--------------------------

We distinguish `In`Terms (into which we push types) and `Ex`Terms (from
which we pull types).

> data Dir    = In | Ex

This is the by-now traditional bidirectional
type-checking @turner:bidirectional_tc story: there are *checkable*
terms that are checked against given types, and there are *inferable*
terms whose types are inferred relative to a typing context. We push
types in to checkable terms, and pull types from inferable terms.

We also distinguish the representations of `TT` terms and `VV` values.

> data Phase  = TT | VV

And, of course, we’re polymorphic in the representation of free
variables, like your mother always told you. This gives the following
signature for a term:

> data Tm :: {Dir, Phase} -> * -> * where

We can push types into:

-   lambda terms;

-   canonical terms; and

-   inferred terms.

>   L     :: Scope p x             -> Tm {In, p}   x -- \(\lambda\)
>   C     :: Can (Tm {In, p} x)    -> Tm {In, p}   x -- canonical
>   N     :: Tm {Ex, p} x          -> Tm {In, p}   x -- `Ex` to |In|

And we can infer types from:

-   parameters, because they carry their types;

-   variables, by reading the context;

-   fully applied operators, by `opTy` defined below;

-   elimination, by the type of the eliminator; and

-   type ascription on a checkable term, by the ascripted type.

>   P     :: x                                    -> Tm {Ex, p}   x -- parameter
>   V     :: Int                                  -> Tm {Ex, TT}  x -- variable
>   (:@)  :: Op -> [Tm {In, p} x]                 -> Tm {Ex, p}   x -- fully applied op
>   (:$)  :: Tm {Ex, p} x -> Elim (Tm {In, p} x)  -> Tm {Ex, p}   x -- elim
>   (:?)  :: Tm {In, TT} x -> Tm {In, TT} x       -> Tm {Ex, TT}  x -- typing
>   Yuk   :: Tm {In, VV} x                        -> Tm {Ex, TT}  x -- dirty

To put some flesh on these bones, we define and use the `Scope`, `Can`,
|Op|, and `Elim` data-types. Their role is described below. Before that,
let us point out an important invariant. Non-implementers are advised to
skip the following.

[Neutral terms and Operators]

In the world of values, i.e. |Tm <span>In, VV</span> p|, the neutral
terms are exactly the |N t| terms. Enforcing this invariant requires
some caution in the way we deal with operators and how we turn them into
values, so this statement relies on the hypothesis that the evaluation
of operators is correct: it is not enforced by Haskell type-system.

To prove that statement, we first show that any |Tm <span>In, VV</span>
p| which is not a |N t| is not a neutral term. This is obvious as we are
left with lambda and canonicals, which cannot be stuck. Then, we have to
prove that a |N t| in |Tm <span>In, VV</span> p| form is a stuck term.
We do so by case analysis on the term `t` inside the `N`:

-   Typing and variables will not let you get values, so a neutral value
    is not one of those.

-   This is also easy if you have a parameter: it is stuck waiting for
    its definition.

-   An eliminator in value form consists in an elimination applied to a
    value in `Ex`, which is – by induction – a neutral term. Hence, the
    eliminator is stuck too.

-   The case for fully applied operator is more problematic: we need one
    of the arguments to be a |N t|, and to be used by `Op`. This way,
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
> f -$ as = N (foldl (\f a -> f :$ A a) (Yuk f) as)

Scopes

A `Scope` represents the body of a binder, but the representation
differs with phase. In *terms*, |x :. t| is a *binder*: the `t` is a de
Bruijn term with a new bound variable 0, and the old ones incremented.
The `x` is just advice for display name selection.

It is important to ensure that `body` computes to a fully evaluated
value, otherwise say “good bye” to strong normalisation.

In both cases, we represent constant functions with |K t|, equivalent of
| \_ -\> t |.

> data Scope :: {Phase} -> * -> * where
>   (:.)  :: String -> Tm {In, TT} x           -> Scope p{-TT-} x  -- binding
>   H     :: Env x -> String -> Tm {In, TT} x    -> Scope p{-VV-} x
>   K     :: Tm {In, p} x                      -> Scope p x     -- constant

Canonical objects

The `Can` functor explains how canonical objects are constructed from
sub-objects (terms or values, as appropriate). Lambda is not included
here: morally, it belongs; practically, adapting `Can` to support
binding complicates the definition. Note the presence of the @import@
She-ism: this means that canonical constructors can be later plugged in
using a She aspect.

> data Can :: * -> * where
>     Set   :: Can t                                   -- set of sets
>     Pi    :: t -> t -> Can t                         -- functions
>     Con   :: t -> Can t                              -- packing
>     Anchors  ::  Can t
>     Anchor   ::  t -> t -> t -> Can t
>     AllowedBy :: t -> Can t
>     AllowedEpsilon :: Can t
>     AllowedCons :: t -> t -> t -> t -> t -> Can t
>     Mu     :: Labelled Id t -> Can t
>     EnumT  :: t -> Can t
>     Ze     :: Can t
>     Su     :: t -> Can t
>     EqBlue :: (t :>: t) -> (t :>: t) -> Can t
>     Monad     :: t -> t -> Can t
>     Return    :: t -> Can t
>     Composite :: t -> Can t
>     IMu     :: Labelled (Id :*: Id) t -> t -> Can t
>     Label  :: t -> t -> Can t
>     LRet   :: t -> Can t
>     Nu :: Labelled Id t -> Can t
>     CoIt :: t -> t -> t -> t -> Can t
>     Prob       :: Can t
>     ProbLabel  :: t -> t -> t -> Can t
>     PatPi      :: t -> t -> t -> Can t
>     Sch        :: Can t
>     SchTy      :: t -> Can t
>     SchExpPi   :: t -> t -> Can t
>     SchImpPi    :: t -> t -> Can t
>     Prop    :: Can t
>     Prf     :: t -> Can t
>     All     :: t -> t -> Can t
>     And     :: t -> t -> Can t
>     Trivial :: Can t
>     Absurd  :: Can t
>     Box     :: Irr t -> Can t
>     Inh     :: t -> Can t
>     Wit     :: t -> Can t
>     Quotient :: t -> t -> t -> Can t
>     Record  :: Labelled Id t -> Can t
>     REmpty  :: Can t
>     RCons   :: t -> t -> t -> Can t
>     RSig    :: Can t
>     Unit   :: Can t
>     Void   :: Can t
>     Sigma  :: t -> t -> Can t
>     Pair   :: t -> t -> Can t
>     UId    :: Can t
>     Tag    :: String -> Can t
>   deriving (Show, Eq)

The `Con` object is used and abused in many circumstances. However, all
ilts usages share the same pattern: `Con` is used whenever we need to
”pack” an object `t` into something else, to avoid ambiguities. For
example, we use `Con` in the following case:
$$\Rule{desc x (Mu x) \ni y}
     {Mu x \ni Con y}$$

Eliminators

The `Elim` functor explains how eliminators are constructed from their
sub-objects. It’s a sort of logarithm @hancock:amen. Projective
eliminators for types with $\eta$-laws go here.

> data Elim :: * -> * where
>   A     :: t -> Elim t                             -- application
>   Out   :: Elim t                                  -- unpacks Con
>   Call   :: t -> Elim t
>   Fst    :: Elim t
>   Snd    :: Elim t
>   deriving (Show, Eq)

Just as `Con` was packing things up, we define here `Out` to unpack
them.

Eliminators can be chained up in a *spine*. A `Spine` is a list of
eliminators for terms, typically representing a list of arguments that
can be applied to a term with the `$:$` operator.

> type Spine p x = [Elim (Tm {In, p} x)]
> ($:$) :: Tm {Ex, p} x -> Spine p x -> Tm {Ex, p} x
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

> telCheck ::  (Alternative m, MonadError (StackError t) m) =>
>              (TY :>: t -> m (s :=>: VAL)) ->
>              (TEL x :>: [t]) -> m ([s :=>: VAL] , x)
> telCheck chev (Target x :>: []) = return ([] , x)
> telCheck chev ((_ :<: sS :-: tT) :>: (s : t)) = do
>     ssv@(s :=>: sv) <- chev (sS :>: s)
>     (svs , x) <- telCheck chev ((tT sv) :>: t)
>     return (ssv : svs , x)
> telCheck _ _ = throwError $ sErr "telCheck: opTy mismatch"

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
> pattern ANCHORS        = C Anchors
> pattern ANCHOR u t ts  = C (Anchor u t ts)
> pattern ALLOWEDBY t    = C (AllowedBy t)
> pattern ALLOWEDEPSILON = C AllowedEpsilon
> pattern ALLOWEDCONS _S _T q s ts = C (AllowedCons _S _T q s ts)
> pattern IDN     = ZE
> pattern CONSTN  = SU ZE
> pattern SUMN    = SU (SU ZE)
> pattern PRODN   = SU (SU (SU ZE))
> pattern SIGMAN  = SU (SU (SU (SU ZE)))
> pattern PIN     = SU (SU (SU (SU (SU ZE))))
> pattern MU l x        = C (Mu (l :?=: Id x))
> pattern IDD           = CON (PAIR IDN     VOID)
> pattern CONSTD x      = CON (PAIR CONSTN  (PAIR x VOID))
> pattern SUMD e b      = CON (PAIR SUMN    (PAIR e (PAIR b VOID)))
> pattern PRODD u d d'  = CON (PAIR PRODN   (PAIR u (PAIR d (PAIR d' VOID))))
> pattern SIGMAD s t    = CON (PAIR SIGMAN  (PAIR s (PAIR t VOID)))
> pattern PID s t       = CON (PAIR PIN     (PAIR s (PAIR t VOID)))
> pattern ZE         = C Ze
> pattern SU n       = C (Su n)
> pattern NILN       = ZE
> pattern CONSN      = SU ZE
> pattern ENUMT e    = C (EnumT e)
> pattern NILE       = CON (PAIR NILN VOID)
> pattern CONSE t e  = CON (PAIR CONSN (PAIR t (PAIR e VOID)))
> pattern EQBLUE p q = C (EqBlue p q)
> pattern MONAD d x   = C (Monad d x)
> pattern RETURN x    = C (Return x)
> pattern COMPOSITE t = C (Composite t)
> pattern IVARN     = ZE
> pattern ICONSTN   = SU ZE
> pattern IPIN      = SU (SU ZE)
> pattern IFPIN     = SU (SU (SU ZE))
> pattern ISIGMAN   = SU (SU (SU (SU ZE)))
> pattern IFSIGMAN  = SU (SU (SU (SU (SU ZE))))
> pattern IPRODN    = SU (SU (SU (SU (SU (SU ZE)))))
> pattern IMU l ii x i  = C (IMu (l :?=: (Id ii :& Id x)) i)
> pattern IVAR i        = CON (PAIR IVARN     (PAIR i VOID))
> pattern IPI s t       = CON (PAIR IPIN      (PAIR s (PAIR t VOID)))
> pattern IFPI s t      = CON (PAIR IFPIN     (PAIR s (PAIR t VOID)))
> pattern ISIGMA s t    = CON (PAIR ISIGMAN   (PAIR s (PAIR t VOID)))
> pattern IFSIGMA s t   = CON (PAIR IFSIGMAN  (PAIR s (PAIR t VOID)))
> pattern ICONST p      = CON (PAIR ICONSTN   (PAIR p VOID))
> pattern IPROD u x y   = CON (PAIR IPRODN    (PAIR u (PAIR x (PAIR y VOID))))
> pattern LABEL l t = C (Label l t)
> pattern LRET t    = C (LRet t)
> pattern NU l t = C (Nu (l :?=: Id t))
> pattern COIT d sty f s = C (CoIt d sty f s)
> pattern PROB             = C Prob
> pattern PROBLABEL u s a  = C (ProbLabel u s a)
> pattern PATPI u s p      = C (PatPi u s p)
> pattern SCH              = C Sch
> pattern SCHTY s          = C (SchTy s)
> pattern SCHEXPPI s t     = C (SchExpPi s t)
> pattern SCHIMPPI s t     = C (SchImpPi s t)
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
> pattern QUOTIENT x r p = C (Quotient x r p)
> pattern CLASS x        = C (Con x)
> pattern RSIG         = C RSig
> pattern REMPTY       = C REmpty
> pattern RCONS s i t  = C (RCons s i t)
> pattern RECORD l s   = C (Record (l :?=: Id s))
> pattern SIGMA p q = C (Sigma p q)
> pattern PAIR  p q = C (Pair p q)
> pattern UNIT      = C Unit
> pattern VOID      = C Void
> pattern Times x y = Sigma x (L (K y))
> pattern TIMES x y = C (Times x y)
> pattern UID    = C UId
> pattern TAG s  = C (Tag s)

We have some type synonyms for commonly occurring instances of `Tm`.

> type InTm   = Tm {In, TT}
> type ExTm   = Tm {Ex, TT}
> type INTM   = InTm REF
> type EXTM   = ExTm REF
> type VAL    = Tm {In, VV} REF
> type TY     = VAL
> type NEU    = Tm {Ex, VV} REF
> type Env x  = (Bwd (Tm {In, VV} x), TXTSUB)  -- values for deBruijn indices
> type ENV    = Env REF
> type TXTSUB = [(Char, String)]        -- renaming plan

We have special pairs for types going into and coming out of stuff. We
write |typ :\>: thing| to say that `typ` accepts the term `thing`,
i.e. we can push the `typ` in the `thing`. Conversely, we write |thing
:\<: typ| to say that `thing` is of inferred type `typ`, i.e.we can pull
the type `typ` out of the `thing`. Therefore, we can read `:\>:` as
“accepts” and `:\<:` as “has inferred type”.

> data ty :>: tm = ty :>: tm  deriving (Show,Eq)
> infix 4 :>:
> data tm :<: ty = tm :<: ty  deriving (Show,Eq)
> infix 4 :<:
> fstIn :: (a :>: b) -> a
> fstIn (x :>: _) = x
> sndIn :: (a :>: b) -> b
> sndIn (_ :>: x) = x
> fstEx :: (a :<: b) -> a
> fstEx (x :<: _) = x
> sndEx :: (a :<: b) -> b
> sndEx (_ :<: x) = x

As we are discussing syntactic sugar, we define the “reduces to” symbol:

> data t :=>: v = t :=>: v deriving (Show, Eq)
> infix 5 :=>:

with the associated projections:

> valueOf :: (t :=>: v) -> v
> valueOf (_ :=>: v) = v
> termOf :: (t :=>: v) -> t
> termOf (t :=>: _) = t

Intuitively, |t :=\>: v| can be read as “the term `t` reduces to the
value `v`”.

We use `(??)` as a smart constructor for type ascriptions that omits
them when the term is in fact neutral.

> (??) :: INTM -> INTM -> EXTM
> (N t) ?? _   = t
> t     ?? ty  = t :? ty

Syntactic Equality {#subsec:Evidences.Tm.syntactic-equality}
------------------

In the following, we implement definitional equality on terms. In this
case, it’s mainly structural.

> instance Eq x => Eq (Tm {d, p} x) where

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

> instance Eq x => Eq (Scope {p} x) where
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

In this section, we have defined the syntactic equality on terms. The
general definition of syntactic equality remains to be done. It is the
subject of Section [sec:Evidences.DefinitionalEquality]: there, we rely
on *quotation* to turn values into terms. Once turned into terms, we
fall back to the equality defined above.

References {#subsec:Evidences.Tm.references}
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
>   show (name := kt) = intercalate "." (map (\(x,n) -> x ++ "_" ++ show n) name) ++ " := " ++ show kt

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

A hole will be in one of three “Buddy Holly” states:

-   `Crying`: the elaboration strategy intended to solve the hole has
    gone wrong.

-   `Waiting`: a solution strategy exists for the hole (including the
    “strategy” of waiting for the user to solve it).

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

For example, labels are used in the presentation of the |Enum|
(Section [sec:Features.Enum]) and `Desc` (Section [sec:Features.Desc])
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

> idVAL :: String -> Tm {In,p} x
> idVAL x   = L (x :. (N (V 0)))
> idTM :: String -> INTM
> idTM = idVAL

> ($#) :: Int -> [Int] -> InTm x
> f $# xs = N (foldl (\ g x -> g :$ A (NV x)) (V f) xs)

The aptly named `\$\#\#` operator applies an `ExTm` to a list of
|InTm|s.

> ($##) :: (Functor t, Foldable t) => ExTm x -> t (InTm x) -> ExTm x
> f $## xs = foldl (\ v w -> v :$ A w) f xs

Sensible name advice is a hard problem. The `fortran` function tries to
extract a useful name from a binder.

> fortran :: Tm {In, p} x -> String
> fortran (L (x :. _))   | not (null x) = x
> fortran (L (H _ x _))   | not (null x) = x
> fortran _ = "xf"

Similarly, it is useful to extract name advice from a `REF`.

> refNameAdvice :: REF -> String
> refNameAdvice = fst . last . refName

If we have a bunch of references we can make them into a spine:

> toSpine :: Foldable f => f REF -> Spine {TT} REF
> toSpine = foldMap (\ r -> [A (NP r)])

Error Stack
-----------

This is a first try, with some shortcomings. Feel free to modify the
following to make it suit your need.

> data ErrorTok t = StrMsg String
>                 | ErrorTm       (t       :<: Maybe t)
>                 | ErrorCan      (Can t)
>                 | ErrorElim     (Elim t)
>                 | ErrorREF REF
>                 | ErrorVAL      (VAL     :<: Maybe TY)
> instance Functor ErrorTok where
>     fmap f (StrMsg x)              = StrMsg x
>     fmap f (ErrorTm (t :<: mt))    = ErrorTm (f t :<: fmap f mt)
>     fmap f (ErrorCan t)   = ErrorCan (fmap f t)
>     fmap f (ErrorElim t)  = ErrorElim (fmap f t)
>     fmap f (ErrorREF r)            = ErrorREF r
>     fmap f (ErrorVAL (t :<: mt))   = ErrorVAL (t :<: mt)

An error is list of error tokens:

> type ErrorItem t = [ErrorTok t]

Errors a reported in a stack, as failure is likely to be followed by
further failures. The top of the stack is the head of the list.

> newtype StackError t = StackError { unStackError :: [ErrorItem t] }

\< instance MonadPlus (Either (StackError a)) where \< mzero = Left
(StackError []) \< mplus x@(Right l) \_ = x \< mplus \_ x = x \< \<
mplus (Left (StackError xs)) (Left (StackError ys)) = \< Left
(StackError (xs++ys)) \< mplus l@(Left (StackError xs)) \_ = l \< mplus
\_ r@(Left (StackError xs)) = r \< mplus (Right l) (Right r) =k

> instance Error (StackError t) where
>   strMsg = sErr
> instance M.Monoid (StackError t) where
>   (StackError a) `mappend` (StackError b) = StackError (a ++ b)
>   mempty = StackError []

To ease the writing of error terms, we have a bunch of combinators:

> err :: String -> ErrorItem t
> err s = [StrMsg s]
> sErr :: String -> StackError t
> sErr = StackError . pure . err
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
> pushError :: MonadError (StackError t) m => m a -> StackError t -> m a
> pushError c e = catchError c (\x -> throwError (e <> x))
> throwErrorS :: MonadError (StackError t) m => [ErrorItem t] -> m a
> throwErrorS = throwError . StackError
> catchMaybe :: MonadError (StackError t) m => Maybe a -> StackError t -> m a
> catchMaybe (Just x) _ = return x
> catchMaybe Nothing  e = throwError e
> catchEither :: MonadError (StackError t) m
>             => Either (StackError t) a
>             -> StackError t
>             -> m a
> catchEither (Right x) _ = return x
> catchEither (Left s) e = throwError (e <> s)

> throwErrorStr :: MonadError (StackError t) m => String -> m a
> throwErrorStr = throwError . StackError . pure . err

TODO(joel) rename to throwErrorTm

> throwError' :: MonadError (StackError t) m => t -> m a
> throwError' = throwError . StackError . pure . errTm

> convertErrorVALs :: ErrorTok VAL -> ErrorTok t
> convertErrorVALs (StrMsg s)             = StrMsg s
> convertErrorVALs (ErrorTm tt)           = ErrorVAL tt
> convertErrorVALs (ErrorCan c)           = ErrorVAL (C c :<: Nothing)
> convertErrorVALs (ErrorElim e)          = StrMsg $ "ErrorElim " ++ show e
> convertErrorVALs (ErrorREF r)           = ErrorREF r
> convertErrorVALs (ErrorVAL tt)          = ErrorVAL tt

> instance Traversable Can where
>     traverse f Set       = (|Set|)
>     traverse f (Pi s t)  = (|Pi (f s) (f t)|)
>     traverse f (Con t)   = (|Con (f t)|)
>     traverse _ Anchors = (| Anchors |)
>     traverse f (Anchor u t ts) = (|Anchor (f u) (f t) (f ts)|)
>     traverse f (AllowedBy t) = (|AllowedBy (f t)|)
>     traverse f AllowedEpsilon = (|AllowedEpsilon|)
>     traverse f (AllowedCons _S _T q s ts) = (|AllowedCons (f _S) (f _T) (f q) (f s) (f ts)|)
>     traverse f (Mu l) = (|Mu (traverse f l)|)
>     traverse f (EnumT e)    = (|EnumT (f e)|)
>     traverse f Ze           = (|Ze|)
>     traverse f (Su n)       = (|Su (f n)|)
>     traverse f (EqBlue (pty :>: p) (qty :>: q)) =
>       (|EqBlue (|(:>:) (f pty) (f p)|) (|(:>:) (f qty) (f q)|)|)
>     traverse f (Monad d x)   = (| Monad (f d) (f x) |)
>     traverse f (Return x)    = (| Return (f x) |)
>     traverse f (Composite x) = (| Composite (f x) |)
>     traverse f (IMu l i)     = (|IMu (traverse f l) (f i)|)
>     traverse f (Label l t) = (| Label (f l) (f t) |)
>     traverse f (LRet t)    = (| LRet (f t) |)
>     traverse f (Nu t) = (|Nu (traverse f t)|)
>     traverse f (CoIt d sty g s) = (|CoIt (f d) (f sty) (f g) (f s)|)
>     traverse _ Prob = (| Prob |)
>     traverse f (ProbLabel u s a) = (|ProbLabel (f u) (f s) (f a)|)
>     traverse f (PatPi u s p) = (|PatPi (f u) (f s) (f p)|)
>     traverse _ Sch = (| Sch |)
>     traverse f (SchTy t)      = (|SchTy (f t)|)
>     traverse f (SchExpPi s t) = (|SchExpPi (f s) (f t)|)
>     traverse f (SchImpPi s t) = (|SchImpPi (f s) (f t)|)
>     traverse _ Prop      = (|Prop|)
>     traverse f (Prf p)   = (|Prf (f p)|)
>     traverse f (All p q) = (|All (f p) (f q)|)
>     traverse f (And p q) = (|And (f p) (f q)|)
>     traverse _ Trivial   = (|Trivial|)
>     traverse _ Absurd    = (|Absurd|)
>     traverse f (Box p)   = (|Box (traverse f p)|)
>     traverse f (Inh ty)  = (|Inh (f ty)|)
>     traverse f (Wit t)   = (|Wit (f t)|)
>     traverse f (Quotient x r p) = (| Quotient (f x) (f r) (f p) |)
>     traverse f RSig           = (|RSig|)
>     traverse f REmpty         = (|REmpty|)
>     traverse f (RCons s i t)  = (|RCons (f s) (f i) (f t)|)
>     traverse f Unit         = (|Unit|)
>     traverse f Void         = (|Void|)
>     traverse f (Sigma s t)  = (|Sigma (f s) (f t)|)
>     traverse f (Pair x y)   = (|Pair (f x) (f y)|)
>     traverse f UId          = (|UId|)
>     traverse f (Tag s)      = (|(Tag s)|)

> instance HalfZip Can where
>     halfZip Set        Set        = Just Set
>     halfZip (Pi s1 t1) (Pi s2 t2) = Just $ Pi (s1,s2) (t1,t2)
>     halfZip (Con t1)   (Con t2)   = Just $ Con (t1,t2)
>     halfZip Anchors Anchors = Just Anchors
>     halfZip (Anchor u1 t1 ts1) (Anchor u2 t2 ts2) = Just $ Anchor (u1, u2) (t1, t2) (ts1, ts2)
>     halfZip (AllowedBy t1) (AllowedBy t2) = Just $ AllowedBy (t1, t2)
>     halfZip AllowedEpsilon AllowedEpsilon = Just $ AllowedEpsilon
>     halfZip (AllowedCons _S1 _T1 q1 s1 ts1) (AllowedCons _S2 _T2 q2 s2 ts2) = Just $ AllowedCons (_S1, _S2) (_T1, _T2) (q1, q2) (s1, s2) (ts1, ts2)
>     halfZip (Mu t0) (Mu t1) = (| Mu (halfZip t0 t1) |)
>     halfZip (EnumT t0) (EnumT t1) = Just (EnumT (t0,t1))
>     halfZip Ze Ze = Just Ze
>     halfZip (Su t0) (Su t1) = Just (Su (t0,t1))
>     halfZip (Monad d1 x1) (Monad d2 x2) = Just (Monad (d1, d2) (x1, x2))
>     halfZip (Return x) (Return y) = Just (Return (x, y))
>     halfZip (Composite x) (Composite y) = Just (Composite (x, y))
>     halfZip (IMu l0 i0) (IMu l1 i1) = (|(\p -> IMu p (i0,i1)) (halfZip l0 l1)|)
>     halfZip (Label l1 t1) (Label l2 t2) = Just (Label (l1,l2) (t1,t2))
>     halfZip (LRet x) (LRet y)           = Just (LRet (x,y))
>     halfZip (Nu t0) (Nu t1)  = (| Nu (halfZip t0 t1) |)
>     halfZip (CoIt d0 sty0 g0 s0) (CoIt d1 sty1 g1 s1) =
>       Just (CoIt (d0,d1) (sty0,sty1) (g0,g1) (s0,s1))
>     halfZip Prob Prob = Just Prob
>     halfZip (ProbLabel u1 s1 a1) (ProbLabel u2 s2 a2) = Just $ ProbLabel (u1, u2) (s1, s2) (a1, a2)
>     halfZip (PatPi u1 s1 p1) (PatPi u2 s2 p2) = Just $ PatPi (u1, u2) (s1, s2) (p1, p2)
>     halfZip Sch Sch = Just Sch
>     halfZip (SchTy s1) (SchTy s2) = Just $ SchTy (s1, s2)
>     halfZip (SchExpPi s1 t1) (SchExpPi s2 t2) = Just $ SchExpPi (s1, s2) (t1, t2)
>     halfZip (SchImpPi s1 t1) (SchImpPi s2 t2) = Just $ SchImpPi (s1, s2) (t1, t2)
>     halfZip  Prop      Prop      = Just Prop
>     halfZip  (Prf p0)  (Prf p1)  = Just (Prf (p0, p1))
>     halfZip (Quotient x r p) (Quotient y s q) = Just (Quotient (x, y) (r, s) (p, q))
>     halfZip RSig              RSig              = Just RSig
>     halfZip REmpty            REmpty            = Just REmpty
>     halfZip (RCons s0 i0 t0)  (RCons s1 i1 t1)  =
>       Just (RCons (s0,s1) (i0,i1) (t0,t1))
>     halfZip Unit Unit = Just Unit
>     halfZip (Sigma s0 t0) (Sigma s1 t1) = Just (Sigma (s0,s1) (t0,t1))
>     halfZip Void Void = Just Void
>     halfZip (Pair s0 t0) (Pair s1 t1) = Just (Pair (s0,s1) (t0,t1))
>     halfZip UId UId = Just UId
>     halfZip (Tag s) (Tag s') | s == s' = Just (Tag s)
>     halfZip _          _          = Nothing
> instance Traversable Elim where
>   traverse f (A s)  = (|A (f s)|)
>   traverse _ Out    = (|Out|)
>   traverse f (Call l) = (| Call (f l) |)
>   traverse f Fst  = (|Fst|)
>   traverse f Snd  = (|Snd|)
> instance HalfZip Elim where
>   halfZip (A s) (A t)  = Just $ A (s, t)
>   halfZip (Call t1) (Call t2) = Just (Call (t1, t2))
>   halfZip Fst Fst = (|Fst|)
>   halfZip Snd Snd = (|Snd|)
>   halfZip _ _          = Nothing
> instance Traversable Irr where
>   traverse f (Irr x) = (|Irr (f x)|)

> instance Show x => Show (Tm dp x) where
>   show (L s)       = "L (" ++ show s ++ ")"
>   show (C c)       = "C (" ++ show c ++ ")"
>   show (N n)       = "N (" ++ show n ++ ")"
>   show (P x)       = "P (" ++ show x ++ ")"
>   show (V i)       = "V " ++ show i
>   show (n :$ e)    = "(" ++ show n ++ " :$ " ++ show e ++ ")"
>   show (op :@ vs)  = "(" ++ opName op ++ " :@ " ++ show vs ++ ")"
>   show (t :? y)    = "(" ++ show t ++ " :? " ++ show y ++ ")"
>   show (Yuk v)     = "((" ++ show v ++ "))"
> instance Show x => Show (Scope p x) where
>   show (x :. t)   = show x ++ " :. " ++ show t
>   show (H g x t) = "H (" ++ show g ++ ") " ++ x ++ "(" ++ show t ++ ")"
>   show (K t) = "K (" ++ show t ++")"
> instance Show Op where
>   show = opName
> instance Traversable (Scope {p}) where
>   traverse f (x :. t)   = (|(x :.) (traverse f t)|)
>   traverse f (K t)      = (|K (traverse f t)|)
>   traverse f (H (e, s) x t)  = (|H (| (traverse (traverse f) e) , ~s|) ~x (traverse f t)|)
> instance Traversable f => Traversable (Labelled f) where
>   traverse f (mt :?=: ft)  = (| traverse f mt :?=: traverse f ft |)
> instance (Traversable f, HalfZip f) => HalfZip (Labelled f) where
>   halfZip (Just a  :?=: fs)  (Just b :?=: ft)  =
>     (| (Just (a, b)  :?=:) (halfZip fs ft) |)
>   halfZip (_       :?=: fs)  (_      :?=: ft)  =
>     (| (Nothing  :?=:) (halfZip fs ft) |)
> instance Traversable (Tm {d,p}) where
>   traverse f (L sc)     = (|L (traverse f sc)|)
>   traverse f (C c)      = (|C (traverse (traverse f) c)|)
>   traverse f (N n)      = (|N (traverse f n)|)
>   traverse f (P x)      = (|P (f x)|)
>   traverse f (V i)      = pure (V i)
>   traverse f (t :$ u)   = (|(:$) (traverse f t) (traverse (traverse f) u)|)
>   traverse f (op :@ ts) = (|(op :@) (traverse (traverse f) ts)|)
>   traverse f (tm :? ty) = (|(:?) (traverse f tm) (traverse f ty)|)
