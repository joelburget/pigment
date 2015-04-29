<a name="Evidences.TypeChecker">Type-checker</a>
============

> {-# LANGUAGE TypeOperators, GADTs, KindSignatures, FlexibleInstances,
>     TypeSynonymInstances, FlexibleContexts, PatternGuards,
>     MultiParamTypeClasses, ScopedTypeVariables, PatternSynonyms #-}

> module Evidences.TypeChecker where

> import Control.Applicative
> import Control.Monad.Trans.Class
> import Data.Functor.Identity
> import Data.Monoid ((<>))
> import Data.Traversable

> import Control.Error

> import Kit.BwdFwd
> import Kit.MissingLibrary
> import Evidences.Tm
> import Evidences.Mangler
> import Evidences.Eval
> import {-# SOURCE #-} Evidences.DefinitionalEquality
> import Evidences.Operators
> import NameSupply.NameSupplier

Type-checking Canonicals and Eliminators
----------------------------------------

Canonical objects

Historically, canonical terms were type-checked by the following
function:

    canTy :: (t -> VAL) -> (Can VAL :>: Can t) -> Maybe (Can (TY :>: t))
    canTy ev (Set :>: Set)    = Just Set
    canTy ev (Set :>: Pi s t) = Just (Pi (SET :>: s) ((ARR (ev s) SET) :>: t)
    canTy _  _            = Nothing

If we temporally forget Features, we have here a type-checker that takes
an evaluation function `ev`, a type, and a term to be checked against
this type. When successful, the result of typing is a canonical term
that contains both the initial term and its normalized form, as we get
it for free during type-checking.

However, to avoid re-implementing the typing rules in various places, we
had to generalize this function. The generalization consists in
parameterizing `canTy` with a type-directed function `TY :>: t -> s`,
which is equivalent to `TY -> t -> s`. Because we still need an
evaluation function, both functions are fused into a single one, of
type: `TY :>: t -> (s, VAL)`. To support failures, we extend this type
to `TY :>: t -> m (s, VAL)` where `m` is a `MonadError`.

Hence, by defining an appropriate function `chev`, we can recover the
previous definition of `canTy`. We can also do much more: intuitively,
we can write any type-directed function in term of `canTy`. That is, any
function traversing the types derivation tree can be expressed using
`canTy`.

> -- | Type-check canonical terms
> canTy :: (Monad m, Functor m, Applicative m, ErrorStack m t)
>       => (TY :>: t -> m (s :=>: VAL))
>       -- ^ An evaluator function.
>       --
>       --   "chev" = check / eval
>       --
>       --   Start with a standard evaluator @t -> VAL@ and fuse it with the
>       --   type-directed function @TY :>: t -> s@, then generalize to support
>       --   failures.
>       -> (Can VAL :>: Can t)
>       -- ^ The typechecking problem
>       -> m (Can (s :=>: VAL))
> canTy chev (Set :>: Set)     = return Set
> canTy chev (Set :>: Pi s t)  = do
>     ssv@(s :=>: sv) <- chev (SET :>: s)
>     ttv@(t :=>: tv) <- chev (ARR sv SET :>: t)
>     return $ Pi ssv ttv

Extensions:

> canTy chev (Set :>: Anchors) = return Anchors
> canTy chev (Anchors :>: Anchor u t ts) = do
>     uuv <- chev (UID :>: u)
>     ttv@(t :=>: tv) <- chev (SET :>: t)
>     tstsv <- chev (ALLOWEDBY tv :>: ts)
>     return $ Anchor uuv ttv tstsv
> canTy chev (Set :>: AllowedBy t) = do
>     ttv <- chev (SET :>: t)
>     return $ AllowedBy ttv
> canTy chev (AllowedBy t :>: AllowedEpsilon) = do
>     return $ AllowedEpsilon
> canTy chev (AllowedBy ty :>: AllowedCons _S _T q s ts) = do
>     _SSv@(_S :=>: _Sv) <- chev (SET :>: _S)
>     _TTv@(_T :=>: _Tv) <- chev (ARR _Sv SET :>: _T)
>     qqv <- chev (PRF (EQBLUE (SET :>: ty) (SET :>: PI _Sv _Tv)) :>: q)
>     ssv@(s :=>: sv) <- chev (_Sv :>: s)
>     tstsv <- chev (ALLOWEDBY (_Tv $$ (A sv)) :>: ts)
>     return $ AllowedCons _SSv _TTv qqv ssv tstsv
> canTy chev (Set :>: Mu (ml :?=: Identity x))     = do
>     mlv <- traverse (chev . (ANCHORS :>:)) ml
>     xxv@(x :=>: xv) <- chev (desc :>: x)
>     return $ Mu (mlv :?=: Identity xxv)
> canTy chev (t@(Mu (_ :?=: Identity x)) :>: Con y) = do
>     yyv@(y :=>: yv) <- chev (descOp @@ [x, C t] :>: y)
>     return $ Con yyv
> canTy chev (Set :>: EnumT e)  = do
>     eev@(e :=>: ev) <- chev (enumU :>: e)
>     return $ EnumT eev
> canTy _ (EnumT (CON e) :>: Ze)       | CONSN <- e $$ Fst  = return Ze
> canTy chev (EnumT (CON e) :>: Su n)  | CONSN <- e $$ Fst  = do
>     nnv@(n :=>: nv) <- chev (ENUMT (e $$ Snd $$ Snd $$ Fst) :>: n)
>     return $ Su nnv
> canTy chev (Prop :>: EqBlue (y0 :>: t0) (y1 :>: t1)) = do
>     y0y0v@(y0 :=>: y0v) <- chev (SET :>: y0)
>     t0t0v@(t0 :=>: t0v) <- chev (y0v :>: t0)
>     y1y1v@(y1 :=>: y1v) <- chev (SET :>: y1)
>     t1t1v@(t1 :=>: t1v) <- chev (y1v :>: t1)
>     return $ EqBlue (y0y0v :>: t0t0v) (y1y1v :>: t1t1v)
> canTy chev (Prf (EQBLUE (y0 :>: t0) (y1 :>: t1)) :>: Con p) = do
>     ppv@(p :=>: pv) <- chev (PRF (eqGreen @@ [y0, t0, y1, t1]) :>: p)
>     return $ Con ppv
> canTy chev (Set :>: Monad d x) = do
>     ddv@(d :=>: dv) <- chev (desc :>: d)
>     xxv@(x :=>: xv) <- chev (SET :>: x)
>     return $ Monad ddv xxv
> canTy chev (Monad d x :>: Return v) = do
>     vvv@(v :=>: vv) <- chev (x :>: v)
>     return $ Return vvv
> canTy chev (Monad d x :>: Composite y) = do
>     yyv@(y :=>: yv) <- chev (descOp @@ [d, MONAD d x] :>: y)
>     return $ Composite yyv
> canTy chev (Set :>: IMu (ml :?=: (Identity ii :& Identity x)) i)  = do
>     iiiiv@(ii :=>: iiv) <- chev (SET :>: ii)
>     mlv <- traverse (chev . (ARR iiv ANCHORS :>:)) ml
>     xxv@(x :=>: xv) <- chev (ARR iiv (idesc $$ A iiv) :>: x)
>     iiv <- chev (iiv :>: i)
>     return $ IMu (mlv :?=: (Identity iiiiv :& Identity xxv)) iiv
> canTy chev (IMu tt@(_ :?=: (Identity ii :& Identity x)) i :>: Con y) = do
>     yyv <- chev (idescOp @@ [ ii
>                             , x $$ A i
>                             , L $ "i" :. (let i = 0 in
>                                 C (IMu (fmap (-$ []) tt) (NV i)) )
>                             ] :>: y)
>     return $ Con yyv
> canTy chev (Set :>: Label l t) = do
>     ttv@(t :=>: tv) <- chev (SET :>: t)
>     llv@(l :=>: lv) <- chev (tv :>: l)
>     return (Label llv ttv)
> canTy chev (Label l ty :>: LRet t) = do
>     ttv@(t :=>: tv) <- chev (ty :>: t)
>     return (LRet ttv)
> canTy chev (Set :>: Nu (ml :?=: Identity x))     = do
>     mlv <- traverse (chev . (SET :>:)) ml
>     xxv@(x :=>: xv) <- chev (desc :>: x)
>     return $ Nu (mlv :?=: Identity xxv)
> canTy chev (t@(Nu (_ :?=: Identity x)) :>: Con y) = do
>     yyv <- chev (descOp @@ [x, C t] :>: y)
>     return $ Con yyv
> canTy chev (Nu (_ :?=: Identity x) :>: CoIt d sty f s) = do
>     dv <- chev (desc :>: d)
>     sstyv@(sty :=>: styv) <- chev (SET :>: sty)
>     fv <- chev (ARR styv (descOp @@ [x,styv]) :>: f)
>     sv <- chev (styv :>: s)
>     return (CoIt dv sstyv fv sv)
> canTy chev (Set :>: Prob) = return Prob
> canTy chev (Prob :>: ProbLabel u s a) = do
>     uuv <- chev (UID :>: u)
>     ssv@(_ :=>: sv) <- chev (SCH :>: s)
>     aav <- chev (argsOp @@ [sv] :>: a)
>     return $ ProbLabel uuv ssv aav
> canTy chev (Prob :>: PatPi u s p) = do
>     uuv <- chev (UID :>: u)
>     ssv <- chev (SET :>: s)
>     ppv <- chev (PROB :>: p)
>     return $ PatPi uuv ssv ppv
> canTy chev (Set :>: Sch) = return Sch
> canTy chev (Sch :>: SchTy s) = do
>     ssv <- chev (SET :>: s)
>     return $ SchTy ssv
> canTy chev (Sch :>: SchExpPi s t) = do
>     ssv@(_ :=>: sv) <- chev (SCH :>: s)
>     ttv <- chev (ARR (schTypeOp @@ [sv]) SCH :>: t)
>     return $ SchExpPi ssv ttv
> canTy chev (Sch :>: SchImpPi s t) = do
>     ssv@(_ :=>: sv) <- chev (SET :>: s)
>     ttv <- chev (ARR sv SCH :>: t)
>     return $ SchImpPi ssv ttv
> canTy _   (Set :>: Prop) = return Prop
> canTy chev  (Set :>: Prf p) = Prf <$> chev (PROP :>: p)
> canTy chev  (Prop :>: All s p) = do
>     ssv@(_ :=>: sv) <- chev (SET :>: s)
>     ppv <- chev (ARR sv PROP :>: p)
>     return $ All ssv ppv
> canTy chev  (Prop :>: And p q) =
>     And <$> chev (PROP :>: p) <*> chev (PROP :>: q)
> canTy _  (Prop :>: Trivial) = return Trivial
> canTy _   (Prop :>: Absurd) = return Absurd
> canTy chev  (Prf p :>: Box (Irr x)) = Box . Irr <$> chev (PRF p :>: x)
> canTy chev (Prf (AND p q) :>: Pair x y) =
>     Pair <$> chev (PRF p :>: x) <*> chev (PRF q :>: y)
> canTy _   (Prf TRIVIAL :>: Void) = return Void
> canTy chev (Prop :>: Inh ty) = Inh <$> chev (SET :>: ty)
> canTy chev (Prf (INH ty) :>: Wit t) = Wit <$> chev (ty :>: t)
> canTy chev (Set :>: Quotient x r p) = do
>     x@(_ :=>: xv) <- chev (SET :>: x)
>     r@(_ :=>: rv) <- chev (ARR xv (ARR xv PROP) :>: r)
>     p@(_ :=>: _ ) <- chev (PRF (equivalenceRelation xv rv) :>: p)
>     return $ Quotient x r p
> canTy chev (Quotient a r p :>: Con x) = do
>     x <- chev (a :>: x)
>     return $ Con x
> canTy chev (Set :>: RSig)  = return $ RSig
> canTy chev (RSig :>: REmpty) = return $ REmpty
> canTy chev (RSig :>: RCons sig id ty) = do
>     ssv@(s :=>: sv) <- chev (RSIG :>: sig)
>     iiv@(i :=>: iv) <- chev (UID :>: id)
>     ttv@(t :=>: tv) <- chev (ARR (recordOp @@ [sv]) SET  :>: ty)
>     return $ RCons ssv iiv ttv
> canTy chev (Set :>: Record (ml :?=: Identity r)) = do
>     mlv <- traverse (chev . (SET :>:)) ml
>     rrv@(r :=>: rv) <- chev (RSIG :>: r)
>     return $ Record (mlv :?=: Identity rrv)
> canTy chev (tv@(Record (_ :?=: Identity x)) :>: Con y) = do
>     yyv@(y :=>: yv) <- chev (recordOp @@ [x] :>: y)
>     return $ Con yyv
> canTy _   (Set :>: Unit) = return Unit
> canTy chev  (Set :>: Sigma s t) = do
>     ssv@(s :=>: sv) <- chev (SET :>: s)
>     ttv@(t :=>: tv) <- chev (ARR sv SET :>: t)
>     return $ Sigma ssv ttv
> canTy _   (Unit :>: Void) = return Void
> canTy chev  (Sigma s t :>: Pair x y) =  do
>     xxv@(x :=>: xv) <- chev (s :>: x)
>     yyv@(y :=>: yv) <- chev ((t $$ A xv) :>: y)
>     return $ Pair xxv yyv
> canTy _  (Set :>: UId)    = return UId
> canTy _  (UId :>: Tag s)  = return (Tag s)

> canTy chev (ty :>: x) = throwStack $ stackItem
>     [ errMsg "canTy: the proposed value "
>     , errCan x
>     , errMsg " is not of type "
>     , errTyVal ((C ty) :<: SET)
>     ]

> -- | More specific type for canTy
> canTy' :: (TY :>: t -> Either (StackError t) (s :=>: VAL))
>        -> (Can VAL :>: Can t)
>        -> Either (StackError t) (Can (s :=>: VAL))
> canTy' = canTy

Eliminators

Type-checking eliminators mirrors `canTy`. `elimTy` is provided with a
checker-evaluator, a value `f` of inferred typed `t`, ie. a `f :<: t`
of `VAL :<: Can VAL`, and an eliminator of `Elim t`. If the operation
is type-safe, we are given back the eliminator enclosing the result of
`chev` and the type of the eliminated value.

it computes the type of the argument, ie. the eliminator, in `Elim (s
:=>: VAL)` and the type of the result in `TY`.

Carefully bring t into scope (we don't really care about m and s) so we
can refer to it in `ErrorItem t`, which disambiguates an instance -
`ErrorList a => Error [a]` vs `Error [ErrorItem INTM]`, which we
want.

> elimTy :: (Monad m, ErrorStack m t)
>        => (TY :>: t -> m (s :=>: VAL))
>        -> (VAL :<: Can VAL)
>        -> Elim t
>        -> m (Elim (s :=>: VAL),TY)

> elimTy chev (f :<: Pi s t) (A e) = do
>     eev@(e :=>: ev) <- chev (s :>: e)
>     return $ (A eev, t $$ A ev)
> elimTy chev (_ :<: t@(Mu (_ :?=: Identity d))) Out =
>     return (Out, descOp @@ [d , C t])
> elimTy chev (_ :<: Prf (EQBLUE (t0 :>: x0) (t1 :>: x1))) Out =
>     return (Out, PRF (eqGreen @@ [t0 , x0 , t1 , x1]))
> elimTy chev (_ :<: (IMu tt@(_ :?=: (Identity ii :& Identity x)) i)) Out =
>     return (Out,
>       idescOp @@ [  ii , x $$ A i
>                  ,  L $ "i" :. (let i = 0 in C (IMu (fmap (-$ []) tt) (NV i)) ) ])
> elimTy chev (_ :<: Label _ t) (Call l) = do
>     llv@(l :=>: lv) <- chev (t :>: l)
>     return (Call llv, t)
> elimTy chev (_ :<: t@(Nu (_ :?=: Identity d))) Out =
>     return (Out, descOp @@ [d , C t])
> elimTy chev (f :<: Prf (ALL p q))      (A e)  = do
>     eev@(e :=>: ev) <- chev (p :>: e)
>     return $ (A eev, PRF (q $$ A ev))
> elimTy chev (_ :<: Prf (AND p q))      Fst    = return (Fst, PRF p)
> elimTy chev (_ :<: Prf (AND p q))      Snd    = return (Snd, PRF q)
> elimTy chev (_ :<: Sigma s t) Fst = return (Fst, s)
> elimTy chev (p :<: Sigma s t) Snd = return (Snd, t $$ A (p $$ Fst))
> elimTy _  (v :<: t) e = throwStack $ stackItem
>     [ errMsg "elimTy: failed to eliminate"
>     , errTyVal (v :<: (C t))
>     , errMsg "with"
>     , errElim e
>     ]

> -- | More specific type for elimTy
> elimTy' :: (TY :>: t -> Either (StackError t) (s :=>: VAL))
>         -> (VAL :<: Can VAL)
>         -> Elim t
>         -> Either (StackError t) (Elim (s :=>: VAL), TY)
> elimTy' = elimTy

Operators

The `opTy` function explains how to interpret the telescope `opTyTel`:
it labels the operator's arguments with the types they must have and
delivers the type of the whole application. To do that, one must be able
to evaluate arguments. It is vital to type-check the sub-terms (left to
right) before trusting the type at the end. This corresponds to the
following type:

    opTy :: forall t. (t -> VAL) -> [t] -> Maybe ([TY :>: t] , TY)
    opTy ev args = (...)

Where we are provided an evaluator `ev` and the list of arguments, which
length should be the arity of the operator. If the type of the arguments
is correct, we return them labelled with their type and the type of the
result.

However, we had to generalize it. Following the evolution of `canTy` in
Section [Evidences.TypeChecker.canTy](#Evidences.TypeChecker.canTy), we have adopted the
following scheme:

> opTy :: forall m t s. (Monad m, ErrorStack m t)
>      => Op
>      -> (TY :>: t -> m (s :=>: VAL))
>      -> [t]
>      -> m ([s :=>: VAL], TY)

First, the `MonadError` constraint allows seamless integration in the
world of things that might fail. Second, we have extended the evaluation
function to perform type-checking at the same time. We also liberalise
the return type to `s`, to give more freedom in the choice of the
checker-evaluator. This change impacts on `exQuote`, `infer`, and
`useOp`. If this definition is not clear now, it should become clear
after the definition of `canTy` in
Section [Evidences.TypeChecker.canTy](#Evidences.TypeChecker.canTy).

> opTy op chev ss
>     | length ss == opArity op
>     = telCheck chev (opTyTel op :>: ss)
> opTy op _ _ =
>     let stack :: StackError t
>         stack = stackItem
>             [ errMsg "operator arity error: "
>             , errMsg $ opName op
>             ]
>     in throwStack stack

> -- | More specific type for opTy
> opTy' :: Op
>       -> (TY :>: t -> Either (StackError t) (s :=>: VAL))
>       -> [t]
>       -> Either (StackError t) ([s :=>: VAL], TY)
> opTy' = opTy

<a name="Evidences.TypeChecker.type-checking">Type checking</a>
-------------

Here starts the bidirectional type-checking story. In this section, we
address the Checking side. In the next section, we implement the
Inference side. Give Conor a white-board, three pens of different
colors, 30 minutes, and you will know what is happening below in the
Edinburgh style. If you can bear with some black-and-white boring
sequents, keep reading.

The checker works as follow. In a valid typing environment $\Gamma$, it
checks that the term $t$ is indeed of type $T$, ie. $t$ can be pushed
into $T$: `T :>: t`:

$$\Gamma \vdash \mbox{TY} \ni \mbox{Tm \{In,.\} p}$$

Technically, we also need a name supply and handle failure with a
convenient monad. Therefore, we jump in the `Check` monad defined in
Section 
[NameSupply.NameSupplier.check-monad](#NameSupply.NameSupplier.check-monad).

> check :: (TY :>: INTM) -> Check INTM (INTM :=>: VAL)

Type-checking a canonical term is rather easy, as we just have to
delegate the hard work to `canTy`. The checker-evaluator simply needs to
evaluate the well-typed terms.

> check (C cty :>: C ctm) = do
>   cc' <- canTy check (cty :>: ctm) -- :: Check INTM (Can (INTM :=>: VAL))
>   return $ C ctm :=>: (C $ fmap valueOf cc')

As for lambda, it is simple too. We wish the code was simple too. But,
hey, it isn't. The formal typing rule is the following:

$$\Rule{x : S \vdash T x \ni t}
     {\Pi S\ T \ni \lambda x . t}$$

As for the implementation, we apply the by-now standard trick of making
a fresh variable `x :<: S` and computing the type `T x`. Then, we simply
have to check that `T x :>: t`.

> check (PI s t :>: L sc) = do
>   freshRef  ("__check" :<: s)
>             (\ref -> check (  t $$ A (pval ref) :>:
>                               underScope sc ref))
>   return $ L sc :=>: (evTm $ L sc)

Formally, we can bring the `Ex` terms into the `In` world with the rule:
$$\Rule{n \in Y  \qquad
      \star \ni W \equiv Y}
     {W \ni n}$$

This translates naturally into the following code:

> check (w :>: N n) = do
>   r <- askNSupply
>   yv :<: yt <- infer n
>   case (equal (SET :>: (w, yt)) r) of
>     True -> return $ N n :=>: yv
>     False ->
>         let stack :: StackError INTM
>             stack = stackItem
>                 [ errMsg "check: inferred type"
>                 , errTyVal (yt :<: SET)
>                 , errMsg "of"
>                 , errTyVal (yv :<: yt)
>                 , errMsg "is not"
>                 , errTyVal (w :<: SET)
>                 ]
>         in throwStack stack

Finally, we can extend the checker with the `Check` aspect. If no rule
has matched, then we have to give up.

> check (PRF (ALL p q) :>: L sc)  = do
>     freshRef  ("" :<: p)
>               (\ref -> check (  PRF (q $$ A (pval ref)) :>:
>                                 underScope sc ref))
>     return $ L sc :=>: (evTm $ L sc)
> check (ty :>: tm) = throwStack $ stackItem
>     [ errMsg "check: type mismatch: type"
>     , errTyVal (ty :<: SET)
>     , errMsg "does not admit"
>     , errTm tm
>     ]

<a name="Evidences.TypeChecker.type-inference">Type inference</a>
--------------

On the inference side, we also have a valid typing environment $\Gamma$
that is used to pull types `TY` out of `Ex` terms:

$$\Gamma \vdash \mbox{Tm \{Ex,.\} p} \in \mbox{TY}$$

This translates into the following signature:

> infer :: EXTM -> Check INTM (VAL :<: TY)

We all know the rule to infer the type of a free variable from the
context: $$\CAxiom{\Gamma, x : A, \Delta \vdash x \in A}$$

In Epigram, parameters carry their types, so it is even easier:

> infer (P x)               = return $ pval x :<: pty x

The rule for eliminators is a generalization of the rule for function
application. Let us give a look at its formal rule:
$$\Rule{f \in \Pi\ S\ T  \qquad
      S \ni x}
     {f x \in {(B x)}^\downarrow}$$

The story is the same in the general case: we infer the eliminated term
`t` and we type-check the eliminator, using `elimTy`. Because `elimTy`
computes the result type, we have inferred the result type.

> infer (t :$ s)           = do
>     val :<: ty <- infer t
>     case ty of
>         C cty -> do
>             (s', ty') <- elimTy check (val :<: cty) s
>             return $ (val $$ (fmap valueOf s')) :<: ty'
>         _ ->
>             let stack :: StackError INTM
>                 stack = stackItem
>                     [ errMsg "infer: inferred type"
>                     , errTyVal (ty :<: SET)
>                     , errMsg "of"
>                     , errTyVal (val :<: ty)
>                     , errMsg "is not canonical."
>                     ]
>             in throwStack stack

Following exactly the same principle, we can infer the result of an
operator application:

> infer (op :@ ts)         = do
>   (vs,t) <- opTy op check ts
>   return $ (op @@ (fmap valueOf vs)) :<: t

Type ascription is formalized by the following rule:
$$\Rule{\star \ni \mbox{ty}  \qquad
      \mbox{ty}^\downarrow \ni t}
     {(t :\in T) \in \mbox{ty}^\downarrow}$$

Which translates directly into the following code:

> infer (t :? ty)           = do
>   _ :=>:  vty  <- check (SET  :>: ty  )
>   _ :=>:  v    <- check (vty  :>: t   )
>   return $ v :<: vty

Obviously, if none of the rule above applies, then there is something
fishy.

> infer _ =
>     let stack :: StackError INTM
>         stack = errMsgStack "infer: unable to infer type"
>     in throwStack stack
