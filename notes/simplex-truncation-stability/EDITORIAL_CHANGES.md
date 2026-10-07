# Editorial changes

The received proof was independently audited before these publication edits. All theorem, proposition, corollary, and proof environments are byte-identical to the received TeX. No displayed formula, numerical constant, hypothesis, or mathematical claim was changed.

The PDF author metadata and author line now describe an AI-assisted research supplement without an unpublished-task label. Task-relative wording was replaced by references to the existing quantitative supplement. The random-simplex literature sentence now specifies stability for the simplex as a maximizer, avoiding confusion with a maximum-volume inscribed simplex.

The complete TeX diff is:

```diff
--- received/proof.tex
+++ proof.tex
@@ -3,7 +3,7 @@
 \usepackage{amsmath,amssymb,amsthm,booktabs,xurl,hyperref}
 \hypersetup{colorlinks=true,linkcolor=blue,urlcolor=blue,
  pdftitle={An exact exponent obstruction for lower-end projection-cone simplex stability},
- pdfauthor={Unpublished research extension of entry005}}
+ pdfauthor={Research supplement to entry005}}
 \newtheorem{theorem}{Theorem}
 \newtheorem{corollary}[theorem]{Corollary}
 \newtheorem{proposition}[theorem]{Proposition}
@@ -12,7 +12,7 @@
 \newcommand{\vol}{\operatorname{vol}}
 \newcommand{\ee}{\mathfrak e}
 \title{An exact exponent obstruction for lower-end projection-cone simplex stability}
-\author{Research extension of entry005; unpublished working note}
+\author{Research supplement to entry005; AI-assisted research note}
 \date{7 October 2026}
 \begin{document}
 \maketitle
@@ -23,7 +23,7 @@
 exponent at most $1/(d-1)$. The example also gives an exact lower bound on the
 constant in the latter estimate at this exponent. This is a necessary limit,
 not a claim that the endpoint exponent has been proved for arbitrary bodies.
-The parent's existing explicit power theorem is not reproved here.
+The existing explicit power theorem in the quantitative supplement is not reproved here.
 
 \section{Conventions and public-source scope}
 
@@ -41,10 +41,10 @@
 product/join recursions and does not replace the lower-end definition or add
 a quantitative lower-end theorem within that versioned package.
 
-During this task the additive quantitative supplement was released publicly
+The additive quantitative supplement is available publicly
 at commit \nolinkurl{6785c1c830f8e19e2eb07b0bb89f4d475a8b154a}.
-Its source defines $a$ and $E$ exactly as above and proves the already
-completed every-maximum-simplex bound with exponent
+Its source defines $a$ and $E$ exactly as above and proves the
+every-maximum-simplex bound with exponent
 $1/[d(d^2+2d+2)]$. Its stated inputs are the v2--v3 invariant identities
 and classical Cauchy and mixed-volume formulas; its manifest pins the
 audited dependency commit
@@ -479,7 +479,7 @@
 
 \medskip\noindent\textbf{Random simplices.}
 Ambrus--B\"or\"oczky's random-simplex stability paper studies uniform
-interior sampling; its maximum-simplex stability result is planar.
+interior sampling; its stability theorem for the simplex as a maximizer is planar.
 Entry005 instead uses determinants for the centered cone-volume law on
 the polar boundary. No identity transporting the relevant defects between
 these sampling models has been established here. The cited theorem is
@@ -508,7 +508,7 @@
 and (31) are proved above. The general upper bound with exponent
 $1/(d-1)$, the exact unrestricted distance in (11), and optimal universal
 constants are not proved. No first-discovery or best-known claim is made.
-The exact obstruction does not conflict with the parent's much smaller
+The exact obstruction is compatible with the quantitative supplement's much smaller
 positive exponent.
 
 \medskip\noindent\textbf{Exact supporting computation.}
```
