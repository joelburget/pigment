---
author:
- |
    Edwin Brady, James Chapman, Pierre-Évariste Dagand,\
    Adam Gundry, Conor McBride, Peter Morris, Ulf Norell, Nicolas Oury
bibliography:
- 'Epitome.bib'
title: An Epigram Implementation
...

> module Epitome where

Introduction
============

*"I believe that the time is ripe for significantly better documentation
of programs, and that we can best achieve this by considering programs
to be works of literature."* Donald Knuth, 1992.

This document is intended to realise this lofty aim for the
implementation of Epigram. Although, given that it is being written by
several different people at once, the plot changes constantly, and it's
currently pushing 300 pages even though it has barely been started, I
don't expect it'll be a best seller.

Epigram is a many faceted beast whose facets are constructed roughly one
on top of the other. This document starts by describing its bowels: the
core type theory which serves as Epigram's language of evidence and into
which programs are elaborated. We then proceed outwards and upwards
until we reach its snorting, wild eyed, and rabid face, a.k.a. the
high-level language.

In the beginning
----------------

In the beginning there was Epigram 1. The Epigram 1 language was
designed by Conor McBride and James McKinna in their weighty paper "The
view from the left"@conor.james:viewfromleft. It descibes a programming
language with support for inductive families and dependent pattern
matching. Notably pattern matching is an added extra to the type theory.
Instead, pattern matching programs in the high level language are
*elaborated* into type theoretic expressions made of traditional
eliminators in the underlying theory. An implementation of Epigram 1 was
written by Conor and with its idiosyncratic emacs interface with 2d
syntax, one could make small experiments. Unfortunately this prototype
implementation proved unscalable and unmaintainable. Since then Agda 2
and Coq's Russell language have assimilated many of Epigram 1's features
and many of Epigram's programs can be written in these two other
languages.

Epigram 2 is not just an attempt at a better implementation of Epigram
1; it has a radically different underlying type theory which supports
interesting features in the high-level language. Firstly, it supports
extensional equality of functions in an intentional theory by using
observational equality. Secondly, it is a closed type theory where new
data definitions are new codes in a universe of datatype descriptions
whose validity is internally guaranteed rather than decreed to be
acceptable by an external checker.

Recommended Reading

The type-checker is a bidirectional one @turner:bidirectional_tc. A
remotely related type-checker has been described in the context of
ETT @chapman:ett.

Normalization is achieved by evaluation @dybjer:nbe
[@dybjer:dependent_types_work]. The implementation has been described in
James Chapman's work @chapman:phd. A graspable introduction to both
normalization by evaluation and bidirectional type-checking à la Epigram
can be found in Boutillier's report @boutillier:report.

The story for names has been told by McBride and
McKinna @mcbride:free_variable. *Ite messa est*.

For containers, there is a lot to say. So, I will not say anything for
the moment.

Concerning the `Desc` universe, Morris et al. @morris:spf wrote a clear
article, covering that topic and much more. In particular, they show why
and how `Box` and `mapBox` can automatically derived from `Desc`.
Conor's work on Ornamemts @mcbride:ornaments builds up from a simplified
`Desc` universe: some insights can be found there too. Finally, the
authoritative source shall be cited: Dybjer et al. on
induction-recursion @dybjer:ir_axiom [@dybjer:ir_algebra; @dybjer:iir].

<a name="language">Language</a>
--------

$$\begin{array}{rll}
{\textsc}{InTm} ::= & \verb!Set!
                & \mbox{Universe of sets} \\
            | & \verb!Prop!
                & \mbox{Universe of propositions} \\
            | & {\langle}\verb!(!{\textsc}{Nom}\verb! : !{\textsc}{InTm} \verb!)!{\rangle}^+\verb! -> ! {\textsc}{InTm}
                & \mbox{\(\Pi\)-type} \\
            | & {\textsc}{InTm} \verb! -> ! {\textsc}{InTm}
                & \mbox{nondependent function type} \\
            | & \verb!\! {\textsc}{Nom}^* \verb! -> ! {\textsc}{InTm}
                & \mbox{\(\lambda\)-abstraction} \\
            | & \verb!:- ! {\textsc}{InTm}
                & \mbox{set of proofs} \\
            | & {\textsc}{NAT} {\langle}\verb!+ ! {\textsc}{InTm}{\rangle}^?
                & \mbox{Elements of enumerations} \\
            | & \verb!con ! {\textsc}{InTm}
                & \mbox{Constructor for inductive definitions} \\
            | & \verb!Sig (!{\textsc}{Sig}\verb!)!
                & \mbox{`record' signature} \\
            | & \verb!()!
                & \mbox{unit} \\
            | & \verb![]!
                & \mbox{void} \\
            | & \verb![!{\textsc}{InTm}^+\:{\langle}\verb!, !{\textsc}{InTm}{\rangle}^?\verb!]!
                & \mbox{tuple} \\
            | & \verb!Enum ! {\textsc}{InTm}
                & \mbox{enumeration} \\
            | & \verb!'! {\textsc}{Nom} \: {\textsc}{InTm}
                & \mbox{tag or (co)data} \\
            | & {\langle}\verb!(!{\textsc}{Nom}\verb! : !{\textsc}{InTm} \verb!)!{\rangle}^+\verb! => ! {\textsc}{InTm}
                & \mbox{propositional \(\forall\)} \\
            | & {\textsc}{InTm} \verb! && ! {\textsc}{InTm}
                & \mbox{propositional And} \\
            | & \verb!TT ! | \verb| FF|
                & \mbox{propositional Trivial and Absurd} \\
            | & \verb!1  ! | \verb| 0|
                & \mbox{proofs of Trivial and Absurd} \\
            | & {\textsc}{ExTm} \verb! == ! {\textsc}{ExTm}
                & \mbox{blue equality} \\
            | & \verb!(!{\textsc}{InTm}\verb!)!
                & \mbox{grouping} \\
            | & {\textsc}{ExTm}
                & \mbox{term with synthesizable type} \medskip \\
{\textsc}{Sig} ::= & \varepsilon
                & \mbox{unit signature} \\
           | & {\langle}{\textsc}{Nom}\verb! : !{\rangle}^? {\textsc}{InTm} \: {\textsc}{SigMore}
                & \Sigma x : S . T \\
{\textsc}{SigMore} ::= & \verb!;! {\textsc}{InTm}
                   & \verb!; T! \mbox{ means } \verb!T!\\
                 & \verb!;! {\textsc}{Sig}
                   & \verb!; S! \mbox{ means } \verb!S!\\
                 & \verb!:-! {\textsc}{InTm}
                   & \verb!:- P! \mbox{ means } \verb!:- P!\\
                 & \verb!:-! {\textsc}{InTm} \: {\textsc}{SigMore}
                   & \verb!:- P S! \mbox{ means } \Sigma \_ . P S \\
{\textsc}{ExTm} ::= & \verb!(: ! {\textsc}{InTm} \verb!)!
                & \mbox{type-cast} \\
            | & {\textsc}{Nom}{\langle}\verb!^!{\textsc}{Nat}{\rangle}^? {\langle}\verb!.! {\textsc}{Nom} {\langle}\verb!^!{\textsc}{Nat}{\rangle}^? {\rangle}^*
                & \mbox{relative name} \\
            | & {\textsc}{ExTm} \: {\textsc}{InTm}
                & \mbox{application} \\
            | & {\textsc}{ExTm}\:\verb|!|
                & \mbox{car} \\
            | & {\textsc}{ExTm}\:\verb!-!
                & \mbox{cdr} \\
            | & {\textsc}{Op}\verb!(!{\textsc}{InTm}^{\verb!,!*}\verb!)!
                & \mbox{operator} \\
            | & \verb!(!{\textsc}{InTm}\verb! : !{\textsc}{InTm}\verb!)!  \verb! <-> ! \verb!(!{\textsc}{InTm}\verb! : !{\textsc}{InTm}\verb!)!
                & \mbox{green equality} \\
\end{array}$$

and more to come. For developments:

$$\begin{array}{rll}
{\textsc}{Top} ::= & {\langle}\verb![! {\textsc}{Girl}^* \verb!]! {\rangle}^? {\textsc}{Com}^{\verb!;!*}
               & \mbox{top-level development} \\

{\textsc}{Girl} ::= & {\textsc}{Nom} {\langle}\verb![! {\textsc}{Line}^* \verb!]! | \verb!:=!  {\rangle}{\langle}\verb!?! | {\textsc}{InTm} {\rangle}\verb!:! {\textsc}{InTm} {\langle}\verb![| ! {\textsc}{Com}^{\verb!;!*} \verb! |]! {\rangle}^? \verb! ;!
               & \mbox{development} \\
           | & {\textsc}{Nom} \verb![! {\textsc}{Line}^* \verb!]! {\langle}\verb![| ! {\textsc}{Com}^{\verb!;!*} \verb! |]! {\rangle}^? \verb! ;!
               & \mbox{module} \\

{\textsc}{Line} ::= & {\textsc}{Girl} | {\textsc}{Boy}
                 & \mbox{line in development} \\

{\textsc}{Boy} ::= & \verb!\! {\textsc}{Nom} \verb!:! {\textsc}{InTm} \verb! ->!
               & \mbox{$\lambda$-boy} \\
           | & \verb!(! {\textsc}{Nom} \verb!:! {\textsc}{InTm} \verb!) ->!
               & \mbox{$\Pi$-boy} \\
           | & \verb!(! {\textsc}{Nom} \verb!:! {\textsc}{InTm} \verb!;) ->!
               & \mbox{$\Sigma$-boy} \\
           | & \verb!:- (! {\textsc}{Nom} \verb!:! {\textsc}{InTm} \verb!) =>!
               & \mbox{$\forall$-boy} \\

\end{array}$$

This is all very tenative. One overriding principle is that we should
stick to ASCII characters throughout. Users may use Unicode if they
wish, but it should not be forced upon them.

The Name Supply
===============

The Evidence Language
=====================

The Display Language
====================

The Proof State
===============

The Proof Tactics
=================

[Elaboration](/Elaboration)
===========

Distillation
============

Cochon
======

The Source Language
===================

Kit
===
