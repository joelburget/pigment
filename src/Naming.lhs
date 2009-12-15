\section{Naming}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Naming (
>        Offs(Rel, Abs), RelName, InTmRN, ExTmRN,
>        christen, christenAbs, christenName, christenREF,
>        resolve,
>        showName, showEntries, showEntriesAbs
>    ) where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.Identity
> import Data.Char
> import Data.Foldable hiding (elem)
> import Data.List
> import Data.Monoid
> import Data.Traversable

> import BwdFwd
> import Developments
> import MissingLibrary
> import Tm

%endif

\subsection{The Naming of Things}

For display and storage purposes, we have a system of local longnames for referring to entries.
Any component of a local name may have a \textasciicircum|n| or |_n| suffix, where |n| is
an integer, representing a relative or absolute offset. A relative
offset \textasciicircum|n| refers to the $n^\mathrm{th}$ occurrence of the name
encountered when searching upwards, so |x|\textasciicircum|0| refers to the same reference
as |x|, but |x|\textasciicircum|1| skips past it and refers to the next thing named |x|.
An absolute offset |_n|, by contrast, refers to the exact numerical
component of the name. 

> data Offs = Rel Int | Abs Int deriving Show
> type RelName = [(String,Offs)]

> type InTmRN = InTm RelName
> type ExTmRN = ExTm RelName


The |showRelName| function converts a relative name to a string by
inserting the appropriate punctuation.

> showRelName :: RelName -> String
> showRelName = intercalate "." . map f
>   where
>     f (x, Rel 0) = x
>     f (x, Rel i) = x ++ "^" ++ show i
>     f (x, Abs i) = x ++ "_" ++ show i

The |showName| function converts a name to a string absolutely (without christening).

> showName :: Name -> String
> showName = showRelName . map (\(x, i) -> (x, Abs i))


The |showEntries| function folds over a bunch of entries, christening them with the
given auncles and current name, and intercalating to produce a comma-separated list.

> showEntries :: (Traversable f, Traversable g) => Entries -> Name -> f (Entry g) -> String
> showEntries aus me = intercalate ", " . foldMap (\(E ref _ _ _) -> [christenREF aus me ref])

The |showEntriesAbs| function works similarly, but uses absolute names instead of
christening them.

> showEntriesAbs :: Traversable f => f (Entry f) -> String
> showEntriesAbs = intercalate ", " . foldMap f
>   where
>     f (E (n := _) _ _ _) = [showName n]


\subsection{Resolving Local Longnames}

We need to resolve local longnames as
references. We resolve \(f.x.y.z\) by searching outwards for $f$, then
inwards for a child $x$, $x$'s child $y$, $y$'s child $z$. References
are fully $\lambda$-lifted, but as $f$'s parameters are held in common
with the point of reference, we automatically supply them.


> resolve :: Entries -> InTm RelName -> Maybe INTM
> resolve es tm = resolver es B0 % tm


The |resolver| function takes a context and a list of binder names, and
produces a mangle that, when applied, attempts to resolve the parameter
names in an |InTmRN| to produce an |InTm REF|, i.e.\ an INTM.

> resolver :: Entries -> Bwd String -> Mangle Maybe RelName REF
> resolver ps vs = Mang
>     {  mangP  = \ x mes -> (| (findLocal ps vs x) $:$ mes |)
>     ,  mangV  = \ _ _ -> Nothing -- what's that index doing here?
>     ,  mangB  = \ x -> resolver ps (vs :< x)
>     }


The |hits| function determines whether a name component matches a
relative name component. It returns |Right ()| if this is the right
name, and |Left x| if the search should continue (to the left) with
new relative name component |x|. (Changing the component allows its
index to be decremented if it is relative.)

> hits :: (String, Int) -> (String, Offs) -> Either (String, Offs) ()
> hits (x, i) (y, o) | x == y = case o of
>   Abs j  | i == j     -> Right  ()
>          | otherwise  -> Left   (y, o)
>   Rel 0               -> Right  ()
>   Rel j               -> Left   (y, Rel (j - 1))
> hits _ yo = Left yo


The |findLocal| function takes a context, a list of binder names and a relative
name to resolve. It first searches the binders for a |Rel| name, and
returns a de Brujin indexed variable if it is present. Otherwise, it calls
|findGlobal| to search the context.

> findLocal :: Entries -> Bwd String -> RelName -> Maybe (ExTm REF)
> findLocal ps B0 sos = findGlobal ps sos
> findLocal ps (xs :< x) [(y, Rel 0)]       | x == y = (|(V 0)|)
> findLocal ps (xs :< x) ((y, Rel i) : sos) | x == y =
>   vinc <$> findLocal ps xs ((y, Rel (i - 1)) : sos)
> findLocal ps (xs :< x) sos = vinc <$> findLocal ps xs sos
>
> vinc :: EXTM -> EXTM
> vinc (V i)  = V (i + 1)
> vinc n      = n


The |findGlobal| function takes a context and a relative name to resolve. It
searches the context for an entry that hits the name, then searches that
entry's children to resolve the next component. 

> findGlobal :: Entries -> RelName -> Maybe EXTM
> findGlobal B0 sos = empty
> findGlobal (xs :< E r x e _) (y : ys) = case hits x y of
>     Right _  -> findChild r (foldMap boy xs) e ys
>     Left y'  -> findGlobal xs (y' : ys)
>   where
>     boy :: Entry Bwd -> Spine {TT} REF
>     boy (E r _ (Boy _) _)  = [A (N (P r))]
>     boy _                = []


The |findChild| function takes a reference to a containing entry, a spine of
shared parameters, an entity |e| and the remainder of a relative name to
resolve. If the remainder is empty, it returns a parameter referring to the
current entry (applied to the shared parameters if appropriate). Otherwise,
the entity should be a |Girl|, and it searches her children for the name.

> findChild :: REF -> Spine {TT} REF -> Entity Bwd -> RelName -> Maybe EXTM
> findChild r  as (Boy _)              []  = (|(P r)|)
> findChild r  as (Girl _ _)           []  = (|(P r $:$ as)|)
> findChild r  as (Boy _)              ys  = empty
> findChild r  as (Girl _ (es, _, _))  ys  = findD es ys as
>   where
>     findD :: Entries -> RelName -> Spine {TT} REF -> Maybe EXTM
>     findD (xs :< E r x e@(Girl _ _) _) (y : ys) as = case hits x y of
>         Right _  -> findChild r as e ys
>         Left y'  -> findD xs (y' : ys) as
>     findD (xs :< E _ x (Boy _) _) (y : ys) as = case hits x y of
>         Right _  -> empty
>         Left y'  -> findD xs (y' : ys) as
>     findD _ sos as = empty


\subsection{Christening (Generating Local Longnames)}

Just as resolution automatically supplies parameters to references
which are actually lifted, so its inverse, \emph{christening}, must
hide parameters to lifted references which can be seen locally. For
example, here

\begin{alltt}
f [
  x : S
  g => t : T
  ] => g : T
\end{alltt}

$g$ is actually represented as $f.g f.x$, but should be displayed as, er, $g$.

Christening is thus the business of choosing a name for a reference in
scope by finding the shortest path to it from the referring term. The
common prefix of the name may thus be omitted, as may any common
parameters.


The |christen| function takea a list of entries in scope (the auncles of the
current location), the name of the current location and a term. It replaces
the variables and parameters of the term with |String| names as described
above, and removes common parameters.

> christen :: Entries -> Name -> INTM -> InTm String
> christen es n tm = christener es n B0 %% tm


The |christenName| and |christenREF| functions do a similar job for names, and
the name part of references, respectively.

> christenName :: Entries -> Name -> Name -> String
> christenName es me target = case mangleP es me B0 target [] of P x -> x
>
> christenREF :: Entries -> Name -> REF -> String
> christenREF es me (target := _) = christenName es me target


The business of christening is actually done by the following mangle, which
does most of its work in the |mangleP| function. 

> christener :: Entries -> Name -> Bwd String -> Mangle Identity REF String
> christener es me vs = Mang
>     {  mangP = \(target := _) as -> pure (mangleP es me vs target (runIdentity as))
>     ,  mangV = \i _ -> pure (P (vs !. i))
>     ,  mangB = \v -> christener es me (vs :< v)
>     }


The |mangleP| function takes a list of entries in scope, the name of the curent
location, a list of local variables, the name of the parameter to christen and a
spine of arguments. It gives an appropriate relative name to the parameter and
applies it to the arguments, dropping any that are shared with the current location.

> mangleP :: Entries -> Name -> Bwd String -> Name -> [Elim (InTm String)] -> ExTm String
> mangleP auncles me vs target args = 
>     let  (prefix, (t, n):targetSuffix) = splitNames me target
>          numBindersToSkip = getSum (foldMap (\x -> if x == t then Sum 1 else Sum 0) vs)
>          (ancestor, commonEntries, i) = findName auncles (prefix++[(t, n)]) t numBindersToSkip
>          args' = drop (bwdLength commonEntries) args
>     in  if targetSuffix == []
>         then  P (showRelName [(t, Rel i)]) $:$ args'
>         else  case ancestor of
>             E _ (x,_) (Boy _) _ ->
>                 error "mangleP: common ancestor is a boy, so it has no children"
>             E _ (x,_) (Girl LETG (kids, _, _)) _ -> 
>                 let  n = (t, Rel i) : (searchKids kids targetSuffix 0)
>                 in   P (showRelName n) $:$ args'


The |searchKids| function searches a list of children to match a name suffix, producing
a relative name corresponding to the suffix. It should be called with the counter set
to zero, which then is incremented to determine the relative offset of each name component.

> searchKids :: Entries -> [(String, Int)] -> Int -> RelName
> searchKids _   []  _ = []
> searchKids B0  _   _ = error "searchKids: ran out of children"
> searchKids (es :< E _ (x, n) entity _) ((y, m):yms) i
>   | (x, n) == (y, m)  = case entity of
>       Boy _                     ->  if yms == []
>                                     then [(x, Rel i)]
>                                     else error "searchKids: it's mad uncle Quentin!"
>       (Girl LETG (kids, _, _))  ->  (x, Rel i):searchKids kids yms 0
>   | x == y            = searchKids es ((y, m):yms) (succ i)
>   | otherwise         = searchKids es ((y, m):yms) i


The |splitNames| function takes two names and returns their common prefix
along with the suffix of the second name.

> splitNames :: Name -> Name -> (Name, [(String, Int)])
> splitNames (x:xs) (y:ys)
>   | x == y        = let (p, s) = splitNames xs ys in (x:p, s)
> splitNames xs ys  = ([], ys)


The |findName| function searches a list of entries for a name, incrementing the
counter each time its string argument appears as the last component of an entry.
It returns the entry found, its prefix in the list of entries, and the count.

> findName :: Entries -> Name -> String -> Int -> (Entry Bwd, Entries, Int)
> findName (es :< e@(E (n := _) (x,_) _ _)) p y i
>   | n == p     = (e, es, i)                         
>   | x == y     = findName es p y (i+1)
>   | otherwise  = findName es p y i
> findName B0 p _ _ = error ("findName: ran out of ancestors seeking " ++ showName p)



Just in case it is useful, here is a simple christener that assigns absolute names.

> christenAbs :: INTM -> InTm String
> christenAbs tm = christenerAbs B0 %% tm

> christenerAbs :: Bwd String -> Mangle Identity REF String
> christenerAbs vs = Mang
>     {  mangP = \(name := _) as -> pure (P (showName name))
>     ,  mangV = \i _ -> pure (P (vs !. i))
>     ,  mangB = \v -> christenerAbs (vs :< v)
>     }