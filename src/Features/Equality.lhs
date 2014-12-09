\section{Equality}
\label{sec:Features.Equality}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module Features.Equality where

%endif


In the display syntax, a blue equality can be between arbitrary DExTms,
rather than ascriptions. To allow this, we add a suitable constructor |DEqBlue|
to DInTm, along with appropriate elaboration and distillation rules.




