<a name="ProofState.Structure.Developments">Developments</a>
============

> {-# LANGUAGE FlexibleInstances, TypeOperators, GADTs , StandaloneDeriving,
>     PatternSynonyms #-}
>
> module ProofState.Structure.Developments where
>
> import Data.List
> import Data.Traversable
> import Kit.BwdFwd
> import NameSupply.NameSupply
> import Evidences.Tm
> import Evidences.Eval
> import Elaboration.ElabProb
> import DisplayLang.Scheme

The `Dev` data-structure
------------------------

A `Dev`elopment is a structure containing entries, some of which may
have their own developments, creating a nested tree-like structure.
Developments can be of different nature: this is indicated by the `Tip`.
A development also keeps a `NameSupply` at hand, for namespace handling
purposes. Initially we had the following definition:

< type Dev = (Bwd Entry, Tip, NameSupply)

but generalised this to allow other `Traversable` functors `f` in place
of `Bwd`, and to store a `SuspendState`, giving:

> data Dev f = Dev  {  devEntries       :: f (Entry f)
>                   ,  devTip           :: Tip
>                   ,  devNSupply       :: NameSupply
>                   ,  devSuspendState  :: SuspendState
>                   }

> deriving instance Show (Dev Fwd)
> deriving instance Show (Dev Bwd)

`Tip`

There are two kinds of Developments available: modules and definitions.
A `Module` is a development that cannot have a type or value, but simply
packs up some other developments. A development holding a definition can
be in one of three states: an `Unknown` of the given type, a `Suspended`
elaboration problem for producing a value of the type (see
section [Elaboration.ElabMonad](#Elaboration.ElabMonad)), or a `Defined` term of the type.
Note that the type is presented as both a term and a value for
performance purposes.

> data Tip
>   = Module
>   | Unknown (INTM :=>: TY)
>   | Suspended (INTM :=>: TY) EProb
>   | Defined INTM (INTM :=>: TY)
>   deriving Show

`Entry`

As mentioned above, a `Dev` is a kind of tree. The branches are
introduced by the container `f (Entry f)` where `f` is Traversable,
typically a backward list.

An `Entry` leaves a choice of shape for the branches. Indeed, it can
either be:

-   an `Entity` with a `REF`, the last component of its `Name` (playing
    the role of a cache, for performance reasons), and the term
    representation of its type, or

-   a module, ie. a `Name` associated with a `Dev` that has no type or
    value

> data EntityAnchor
>     = AnchConc
>     | AnchConNames
>     | AnchConName String
>     | AnchConDescs
>     | AnchDataDesc
>     | AnchDataTy
>     | AnchInd
>     | AnchIndTy
>     | AnchTy String
>     | AnchParTy String
>     | AnchRefine
>     | AnchMotive
>     | AnchMethod
>     | AnchSig
>     | AnchHope
>     | AnchElabInferFully
>     | AnchTau
>     -- Anchors with cryptic names I don't understand
>     | AnchStr String
>     -- "Nothing"
>     | AnchNo

> instance Show EntityAnchor where
>     show AnchConc = "conc"
>     show AnchConNames = "constructor names"
>     show (AnchConName str) = str
>     show AnchConDescs = "constructor descriptions"
>     show AnchDataDesc = "data description"
>     show AnchDataTy = "data type"
>     show AnchInd = "ind"
>     show AnchIndTy = "ind type"
>     show (AnchTy str) = str
>     show (AnchParTy str) = str
>     show AnchRefine = "refine"
>     show AnchMotive = "motive"
>     show AnchMethod = "method"
>     show AnchSig = "sig"
>     show AnchHope = "hope"
>     show AnchElabInferFully = "elab infer fully"
>     show AnchTau = "tau"
>     show (AnchStr str) = str
>     show AnchNo = "AnchNo"

> data Entry f
>   =  EEntity  { ref       :: REF
>               , lastName  :: (String, Int)
>               , entity    :: Entity f
>               , term      :: INTM
>               , anchor    :: EntityAnchor
>               , expanded  :: Bool }
>   |  EModule  { name      :: Name
>               , dev       :: (Dev f)
>               , expanded  :: Bool }

In the Module case, we have already tied the knot, by defining `M` with
a sub-development. In the Entity case, we give yet another choice of
shape, thanks to the `Entity f` constructor. This constructor is defined
in the next section.

Typically, we work with developments that use backwards lists, hence `f`
is `Bwd`:

> type Entries = Bwd (Entry Bwd)

> instance Show (Entry Bwd) where
>     show (EEntity ref xn e t a expanded) = intercalate " "
>         ["E", show ref, show xn, show e, show t, show a, show expanded]
>     show (EModule n d e) = intercalate " " ["M", show n, show d, show e]

> instance Show (Entry Fwd) where
>     show (EEntity ref xn e t a expanded) = intercalate " "
>         ["E", show ref, show xn, show e, show t, show a, show expanded]
>     show (EModule n d e) = intercalate " " ["M", show n, show d, show e]

[Name caching]

We have mentioned above that an Entity `E` caches the last component of
its `Name` in the `(String, Int)` field. Indeed, grabbing that
information asks for traversing the whole `Name` up to the last element:

> mkLastName :: REF -> (String, Int)
> mkLastName (n := _) = last n

As we will need it quite frequently for display purposes, we extract it
once and for all with `lastName` and later rely on the cached version.

`Entity`

An `Entity` is either a `Parameter` or a `Definition`. A `Definition`
can have children, that is sub-developments, whereas a `Parameter`
cannot.

> data Entity f
>   =  Parameter   ParamKind
>   |  Definition  DefKind (Dev f)

For readability, let us collapse the `Entity` into the `Entry` with
these useful patterns:

> pattern EPARAM ref name paramKind term anchor expanded =
>     EEntity ref name (Parameter paramKind) term anchor expanded
> pattern EDEF ref name defKind dev term anchor expanded =
>     EEntity ref name (Definition defKind dev) term anchor expanded

Kinds of Definitions:

A *definition* eventually constructs a term, by a (possibly empty)
development of sub-objects. The `Tip` of this sub-development will be
`Unknown`, `Suspended` or `Defined`.

A programming problem is a special kind of definition: it follows a type
`Scheme` (Section [DisplayLang.Scheme](#DisplayLang.Scheme)), the high-level
type of the function we are implementing.

> data DefKind = LETG |  PROG (Scheme INTM)

> instance Show DefKind where
>     show LETG      = "LETG"
>     show (PROG _)  = "PROG"

Kinds of Parameters:

A *parameter* is either a $\lambda$, $\forall$ or $\Pi$ abstraction. It
scopes over all following entries and the definitions (if any) in the
enclosing development.

> data ParamKind = ParamLam | ParamAll | ParamPi
>       deriving (Show, Eq)

The link between a type and the kind of parameter allowed is defined by
`lambdable`:

> lambdable :: TY -> Maybe (ParamKind, TY, VAL -> TY)
> lambdable (PI s t)         = Just (ParamLam, s, (t $$) . A)
> lambdable (PRF (ALL s p))  = Just (ParamAll, s, \v -> PRF (p $$ A v))
> lambdable _                = Nothing

> instance Show (Entity Bwd) where
>     show (Parameter k) = "Param " ++ show k
>     show (Definition k d) = "Def " ++ show k ++ " " ++ show d
> instance Show (Entity Fwd) where
>     show (Parameter k) = "Param " ++ show k
>     show (Definition k d) = "Def " ++ show k ++ " " ++ show d

Suspension states

Definitions may have suspended elaboration processes attached, indicated
by a `Suspended` tip. These may be stable or unstable. For efficiency in
the scheduler, each development stores the state of its least stable
child.

> data SuspendState = SuspendUnstable | SuspendStable | SuspendNone
>   deriving (Eq, Show, Enum, Ord)
