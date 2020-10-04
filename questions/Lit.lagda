\documentclass[acmsmall,nonacm=true,screen=true]{acmart}
\settopmatter{printfolios=true,printccs=false,printacmref=false}

\begin{document}

\title{Testing literate Agda}

\begin{code}
open import Prelude.Init

f : ℕ → ℕ
f 0       = 0
f (suc n) = n
\end{code}

\end{document}
